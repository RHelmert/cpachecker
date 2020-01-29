/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.cpa.qMultiInterval;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractQueryableState;
import org.sosy_lab.cpachecker.core.interfaces.Graphable;
// import org.sosy_lab.cpachecker.cpa.ifcsecurity.dependencytracking.Variable;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.InvalidQueryException;

/*
 * Important Information: This analysis depends on the class org.sosy_lab.cpachecker.cpa.interval. If the Interval class is changed, this analysis can break.
 */

/**
 * QuantitativeInformationFlowState
 *
 * <p>The state stores information about the Entropy, the probability, the intervals and the
 * mappings
 */
public class MultiIntervalState
    implements Serializable,
        LatticeAbstractState<MultiIntervalState>,
        AbstractQueryableState,
        Graphable {

  // ================================================================================
  // Work  Progress:
  // 1. working with dead paths. everything needs to be erased, so they cant influence the outcome
  // -->
  // Done!
  // 2. Contract information in states
  // Done!
  // 3. Support IF
  // Done
  // 4. Support WHILE
  // can analyse While <--Check
  // can count each single WHILE <--Check!
  // Bounded ModelChecking within WHILE <-- Check!
  // innerwhile <-- check
  // tidy up code <-- check
  // combine if and while (atm endless loop) <--- DONE!
  // loops + nested loops <--Doone!
  // loopbounding <--- Done
  // TODO Bugfixes if present
  //
  // TODO Next implementations:
  // 5. Support Methods/Pointer/structs...

  // ================================================================================

  // IMPORTANT
  // ================================================================================
  // Known Bugs:
  // None at the moment
  // ================================================================================

  // ================================================================================
  // Fixed Bugs:
  // ---------------if we use nested while with a restriction on loopcount and this count is reached
  //                then the analysis will result in an endless loop. (This is because the innerloop
  //                resets the flag which determines if we should leave the loop)
  //                To solve this, we need a better tracking of loops (The problem is for !(x<y) we
  //                enter the loop with pTruthassumption = false. We need a better way to determine
  // when a loop is
  //                entered or when not. )
  // ================================================================================

  // ================================================================================
  // enums
  // ================================================================================
  public enum exitStatus {
    IDLE,
    LEAVING,
    ERROR; // not yet used
  }

  // ================================================================================
  // Vars
  // ================================================================================
  private static boolean intervalsOnly;
  private static final long serialVersionUID = 1L;
  private LogManager logger;
  private StringBuilder s = new StringBuilder();
  MultiIntervalMinMaxMapping minimax;

  // statecounter gname: global number, name: number for the current state set in the constructor.
  // Mostly for bugfinding purpose
  private static int gname = 0;
  private int name;

  // public because this should be easily accessed and changed
  public exitStatus eS = exitStatus.IDLE;

  // Variable for loops
  private boolean loopstart;
  private boolean innerloop;

  /**
   * counter which counts how often the loopstart has been visited(Format[Loophead;number]. E.g.
   * [(N4,5),(N6,7)] means that the loop with Loophead N4 has gone 5 iterations and the nested loop
   * N6 has gone through 7 iterations in this state). With the use of the Logger it is simple to
   * track down bugs if present
   */
  private TreeMap<CFANode, Integer> loopc = new TreeMap<>();

  // the map of minEntropy values. Set on the last state if intervalOnly in properties is set to
  // false
  /** The min-entropy values of a given Variable */
  HashMap<CIdExpression, Double> hMap;

  HashMap<CIdExpression, Double> h2Map;

  /** the intervals of the element */
  private HashMap<CIdExpression, PInterval> ranges;

  // Deprecated
  // after assumptions no join should be executed
  // private boolean assumeState = false;

  // flag for the last state. A state can be last state even if it has a successor.
  // The last state computation is calculated in strengthen(), but after that there can be a join
  // which resulting state isnt handled by the strengthen method any more.
  // So the lastState flagg has to be transferred to the joined state.
  // We also have to save some additional Informations.
  // private boolean lastState = false;

  // ================================================================================
  // configuration
  // ================================================================================

  public int maxLoops = 30;

  // lets keep a minimum of 5 iterations per loop.
  {
    assert (maxLoops >= 3) : "Too restricted loops. We keeep a minimum of 3 iterations per loop";
  }

  // ================================================================================
  // Constructor
  // ================================================================================

  /**
   * Contstructor of an QuantitativeInformationFlowState
   *
   * @param logger Logger
   * @param maxLoops LoopBounds
   * @param intervalsOnly flag that only PIntervals should be calculated
   */
  public MultiIntervalState(LogManager logger, int maxLoops, boolean intervalsOnly) {
    this.logger = logger;
    MultiIntervalState.intervalsOnly = intervalsOnly;
    ranges = new HashMap<>();
    this.maxLoops = maxLoops;
    name = gname;
    gname++;
    // Log.Log2("StateCreated");
  }
  /**
   * Contstructor of an QuantitativeInformationFlowState
   *
   * @param logger Logger
   * @param maxLoops Loopbounds
   */
  public MultiIntervalState(LogManager logger, int maxLoops) {
    this.logger = logger;

    ranges = new HashMap<>();
    this.maxLoops = maxLoops;
    name = gname;
    gname++;
    // Log.Log2("StateCreated");
  }

  // ================================================================================
  // Getter and Setter
  // ================================================================================

  //  public void setDep(SortedSet<CFANode> rContexts) {
  //    dependencies = rContexts;
  //  }
  //
  //  public SortedSet<CFANode> getDep() {
  //    return dependencies;
  //  }

  //  public void setLoopVars(HashSet<Variable> inner) {
  //
  //    innerVars.addAll(inner);
  //
  //  }
  //
  //  public void printVars() {
  //    Log.Log2("These Variables should be set unbound:");
  //    for (Variable var: innerVars) {
  //      Log.Log2(var);
  //      }
  //    }
  //
  //
  //  public void removeVars() {
  //    innerVars = new HashSet<>();
  //  }
  //
  //  public HashSet<Variable> getInnerVars() {
  //    return innerVars;
  //  }
  /**
   * Add a single loop
   *
   * @param n Starnode of the Loop
   */
  public void addLoop(CFANode n) {
    if (loopc.containsKey(n)) {
      loopc.put(n, loopc.get(n) + 1);
      // Log.Log2(loopc);
    } else {
      loopc.put(n, 1);
      // Log.Log2(loopc);
    }
    Log.Log2("Loopcounter increased, now:" + loopc);
  }

  /**
   * Leave the loop and remove the Loopnode and counter
   *
   * @param n the loopnode to remove
   */
  public void resetLoop(CFANode n) {
    // no assert any more
    // assert loopc.containsKey(n);
    loopc.remove(n);
  }

  // check if we are not in a Loop anymore
  /**
   * Checks iff we are in a loop
   *
   * @return true iff we are in a loop
   */
  public boolean inLoop() {
    if (loopc.isEmpty()) {
      assert !innerloop;
      return true;
    }
    return false;
  }

  /**
   * Getter for Loopcound
   *
   * @return the Loopcoundmap {@link #loopc}
   */
  public TreeMap<CFANode, Integer> getLopC() {
    return loopc;
  }


  /**
   * Checks if we have to exit the loop in the next round
   *
   * @return true if yes else false
   */
  public boolean hasToExitNow() {
    for (Entry<CFANode, Integer> ent : loopc.entrySet()) {
      if (ent.getValue() + 1 >= maxLoops) {
        Log.Log2("MaxLoopsReached: " + maxLoops);
        return true;
      }
    }
    return false;
  }

  // Deprecated
  //  /**
  //   * Checks if we have to exit the loop now
  //   *
  //   * @return true if yes else false
  //   */
  //  public boolean hasToBreakNow() {
  //    for (Entry<CFANode, Integer> ent : loopc.entrySet()) {
  //      if (ent.getValue() >= maxLoops) {
  //        return true;
  //      }
  //    }
  //    return false;
  //  }

  public void setLoopstart() {
    loopstart = true;
  }

  public int getName() {
    return name;
  }

  public void setInnterloop(boolean inner) {
    innerloop = inner;
  }

  public boolean isInner() {
    return innerloop;
  }

  public boolean isLoopstart() {
    return loopstart;
  }

  // Deprecated
  //  public void setAssume() {
  //    assumeState = true;
  //  }
  //  public boolean isAssume() {
  //    return assumeState;
  //  }

  //  public void setLast() {
  //    lastState = true;
  //  }

  /**
   * adds another Treemap to the current Range values
   *
   * @param other the other map which will be added
   */
  public void combineMaps(HashMap<CIdExpression, PInterval> other) {
    ranges.putAll(other);
  }

  public void addRange(CIdExpression var, PInterval r) {
    ranges.put(var, r);
  }
  //  public void setMinEntropyMaps(MultiIntervalMinMaxMapping minimax,HashMap<Variable, Double>
  // hMap) {
  //    this.minimax = minimax;
  //    this.hMap  = hMap;
  //  }

  public void removeKey(CIdExpression key) {
    ranges.remove(key);
  }

  public HashMap<CIdExpression, PInterval> getRangeMap() {
    return ranges;
  }

  //
  /*
   * public boolean contains(String str) {
    return contains(new Variable(str));
  }
   */

  /**
   * checks if we have stored already an Interval for the variable v
   *
   * @param v the Variable to check
   * @return true or false
   */
  public boolean contains(CIdExpression v) {
    return ranges.containsKey(v);
  }

  public PInterval getRange(CIdExpression v) {
    return ranges.get(v);
  }

  @Override
  public boolean shouldBeHighlighted() {
    return false;
  }

  @Override
  public String getCPAName() {
    return "qMultiInterval";
  }

  @Override
  public int hashCode() {
    return super.hashCode();
  }

  // ================================================================================
  //  Visualisation
  // ================================================================================
  /**
   * Lets you display some text on the ARG created by CPAchecker. Useful for knowing where we are at
   * certain points and situations in the analysis.
   *
   * @param c the Message you want to display
   */
  public void SendMessage(Object c) {

    s.append(c);
  }

  // ================================================================================
  //  Methods
  // ================================================================================

  /**
   * Checks if two loopiterations are consecutive ones i.e the second one is one iteration ahead.
   *
   * @param loopc1 first loopcount map
   * @param loopc2 second loopcount map
   * @return true if the second loopcound map implies that its exactly one loopiteration further
   */
  public boolean isNextLoop(TreeMap<CFANode, Integer> loopc1, TreeMap<CFANode, Integer> loopc2) {
    if (loopc1.equals(loopc2) || loopc1.size() != loopc2.size()) {
      return false;
    }
    for (Entry<CFANode, Integer> ent : loopc1.entrySet()) {
      assert loopc2.containsKey(ent.getKey()) : loopc1 + " and " + loopc2;
    }
    for (Entry<CFANode, Integer> ent : loopc2.entrySet()) {
      assert loopc1.containsKey(ent.getKey()) : loopc2 + " and " + loopc1;
    }

    if (loopc1.lastEntry().getValue() == loopc2.lastEntry().getValue() - 1) {
      // the second loop is exactly one iteration further
      for (Entry<CFANode, Integer> ent : loopc1.entrySet()) {
        //        Integer entry1 = loopc1.get(ent.getKey());
        //        Integer entry2 = loopc2.get(ent.getKey());
        // if (!(entry1.equals(entry2)) && !(entry1.equals(loopc1.lastEntry()))) {
        // return false;
        // }
        if (!(ent.getKey().equals(loopc2.lastEntry().getKey()))
            && !(loopc2.get(ent.getKey()) == ent.getValue())) {
          // Log.Log2("false val");
          return false;
        }
      }
      return true;
    }
    return false;
  }
  /**
   * Checks if two loopiterations are consecutive ones i.e the second one is one iteration ahead.
   *
   * @param loopc1 first loopcount map
   * @param loopc2 second loopcount map
   * @return true if the second loopcound map implies that its exactly one loopiteration further
   */
  public boolean newOuterLoopIt(
      TreeMap<CFANode, Integer> loopc1, TreeMap<CFANode, Integer> loopc2) {
    if (loopc1.equals(loopc2) || loopc1.size() != loopc2.size() || loopc1.size() < 2) {
      return false;
    }
    for (Entry<CFANode, Integer> ent : loopc1.entrySet()) {
      assert loopc2.containsKey(ent.getKey()) : loopc1 + " and " + loopc2;
    }
    for (Entry<CFANode, Integer> ent : loopc2.entrySet()) {
      assert loopc1.containsKey(ent.getKey()) : loopc2 + " and " + loopc1;
    }
    for (Entry<CFANode, Integer> ent : loopc1.entrySet()) {
      // if (loopc2.lastEntry().getValue() == 1) {
      // if (loopc2.lowerEntry(loopc2.lastEntry().getKey()).getValue()
      // - 1 == loopc1.lowerEntry(loopc1.lastEntry().getKey()).getValue()) {
      // return true;
      // }
      // }
      if (!ent.getKey().equals(loopc1.firstKey()) && loopc2.get(ent.getKey()) == 1) {
        if (loopc2.lowerEntry(ent.getKey()).getValue() - 1
            == loopc1.lowerEntry(ent.getKey()).getValue()) {
          return true;
        }
      }
    }
    return false;
  }

  @Override
  public String toDOTLabel() {
    StringBuilder sb = new StringBuilder();

    sb.append("\n");

    // first the ranges (Intervals)
    for (Entry<CIdExpression, PInterval> entry : ranges.entrySet()) {
      sb.append("Var:" + entry.getKey() + ",   Range: " + entry.getValue() + "\n");
    }

    // just a test on how much state were created
    // sb.append(name + ". TestState like all");

    if (hMap != null) {
      sb.append("\n MinEntropy: \n");
      for (CIdExpression v : hMap.keySet()) {
        sb.append(
            "Min-Entropy for "
                + v
                + " is: "
                + hMap.get(v)
                + " allowed is minimum "
                + minimax.getMinMinEntMap().get(v.getName())
                + "\n");
      }
    }
    // for testing
    sb.append("\n Loopstart: " + loopstart);
    // flag if we are in a loop
    sb.append("\n innerloop: " + innerloop);
    // counter for loopiterations
    sb.append("\n LoopNodes" + loopc);

    // sb.append("\n this CFA: " + thisNode);
    sb.append("\n Status: " + eS);
    // sb.append("\n Dependencies: " + dependencies);
    sb.append("\n Additional:" + s.toString());
    //    sb.append("\n LoopVars:" + innerVars);

    return sb.toString();
  }

  @Override
  public String toString() {
    return toDOTLabel();
  }


  @Override
  public MultiIntervalState join(MultiIntervalState pOther)
      throws CPAException, InterruptedException {
    MultiIntervalState joinState = new MultiIntervalState(logger, maxLoops);

    // if both of the states are in a loop the resulting state is also in a loop (with the same
    // loopcounter, see the last comment in this method)

    // info: maybe take as condition for join the dependencies additionally to the loopcountermap

    // This is a merge with a loopstart, so we have a special merge
    if (isLoopstart() && name < pOther.name) {
      //      Log.Log2("HeadMerge current " + pOther.innerVars);
      joinState.setLoopstart();
      joinState.loopc = new TreeMap<>(pOther.getLopC());
      Log.Log2(loopc);
      joinState.combineMaps(pOther.getRangeMap());
      //      joinState.setLoopVars(pOther.innerVars);
      joinState.eS = pOther.eS;

      return joinState;

    } else if (pOther.isLoopstart() && name > pOther.name) {
      //      Log.Log2("HeadMerge current " + innerVars);
      joinState.setLoopstart();
      joinState.loopc = new TreeMap<>(loopc);
      //      Log.Log2(loopc);
      joinState.combineMaps(ranges);
      //      joinState.setLoopVars(innerVars);
      joinState.eS = eS;

      return joinState;
    }


    // merge two states to the second one if the loopiteration is one ahead
    if (innerloop || pOther.isInner()) {
      joinState.setInnterloop(true);
      //      if (!loopc.equals(pOther.loopc)) {
      //        return null;
      //      }
      if (isNextLoop(loopc, pOther.loopc)) {
        return pOther;
        // joinState.loopc = (TreeMap<CFANode, Integer>) pOther.getLopC().clone();
        // joinState.combineMaps(pOther.getRangeMap());
        // joinState.eS = pOther.eS;
        // return joinState;
      }
      if (isNextLoop(pOther.loopc, loopc)) {
        return this;
        // joinState.loopc = (TreeMap<CFANode, Integer>) loopc.clone();
        // joinState.combineMaps(ranges);
        // joinState.eS = eS;

        // return joinState;
      }
      //
      if (newOuterLoopIt(loopc, pOther.loopc)) {
        return pOther;
        //        joinState.loopc = (TreeMap<CFANode, Integer>) pOther.getLopC().clone();
        //        joinState.combineMaps(pOther.getRangeMap());
        //        joinState.eS = pOther.eS;
        //        return joinState;
      }
      if (newOuterLoopIt(pOther.loopc, loopc)) {
        return this;
        //        joinState.loopc = (TreeMap<CFANode, Integer>) loopc.clone();
        //        joinState.combineMaps(ranges);
        //        joinState.eS = eS;
        //
        //        return joinState;
      }
    }
    //    Log.Log2("Normal join" + innerloop + "" + pOther.innerloop);
    // else we just merge the maps
    joinState.combineMaps(TreeMultimapOperations.easySumm(ranges, pOther.getRangeMap()));

    // this works because if the loopcounter of the two states are different lessOrEqual will be
    // false and the states wont be merged

    joinState.loopc = new TreeMap<>(loopc);
    //    joinState.innerVars = (HashSet<Variable>) innerVars.clone();
    //    joinState.innerVars.addAll(pOther.innerVars);

    // special case where two last states got merged.
    //    if (lastState && pOther.lastState) {
    //      lastState = true;
    //    }

    if (eS == exitStatus.IDLE) {
      joinState.eS = pOther.eS;
    } else {
      joinState.eS = eS;
    }
    return joinState;
    }


  @Override
  public boolean isLessOrEqual(MultiIntervalState pOther)
      throws CPAException, InterruptedException {

    if (pOther == null) {
      return false;
    }


    if (isNextLoop(loopc, pOther.loopc)) {
      Log.Log2("Next " + loopc + " & " + pOther.loopc);
      return true;
    }
    if (!(loopc.equals(pOther.loopc))) {
      return false;
    }

    // Deprecated
    // No join after an assume edge. Unpredictable behaviour
    //    if (assumeState || pOther.isAssume()) {
    //          return false;
    //    }

    // forceJoin if one of them is a Loopstart
    if (isLoopstart() || pOther.isLoopstart()) {
      // Log.Log2("--------LoopStart------Return TRUE");
      return true;
    }

    // handle leq in Loops
    //    if ((innerloop && pOther.isInner())) {
    //      if (loopc.equals(pOther.loopc)) {
    //        TreeMap<Variable, PInterval> tempTM = pOther.getRangeMap();
    //        Set<Entry<Variable, PInterval>> th = ranges.entrySet();
    //        for (Entry<Variable, PInterval> ent : th) {
    //          if (!(tempTM.get(ent.getKey()).contains(ent.getValue()))) {
    //            return false;
    //          }
    //        }
    //        return true;
    //      }
    //      return false;
    //    }

    // normal leq
    HashMap<CIdExpression, PInterval> tempTM = pOther.getRangeMap();
    Set<Entry<CIdExpression, PInterval>> th = ranges.entrySet();
    for (Entry<CIdExpression, PInterval> ent : th) {
      if (!(tempTM.get(ent.getKey()).contains(ent.getValue()))) {
        return false;
      }
    }
    return true;
    }

  @Override
  public boolean equals(Object pOther) {
    if (!(pOther instanceof MultiIntervalState)) {
      return false;
    }
    return (ranges.equals(((MultiIntervalState) pOther).getRangeMap()));
  }


  @Override
  public MultiIntervalState clone() {
    MultiIntervalState clone = new MultiIntervalState(logger, maxLoops);
    clone.combineMaps(cloneTM(ranges));
    clone.setInnterloop(innerloop);
    //    clone.innerVars = (HashSet<Variable>)innerVars.clone();

    //    clone.loopcounter = loopcounter;
    clone.loopc = new TreeMap<>(loopc);

    //  deprecated
    //    if (assumeState) {
    //      clone.setAssume();
    //    }

    clone.eS = eS;
    return clone;
  }

  /**
   * @param toClone TreeMultimap to clone
   * @return a shallow copy of the Multimap
   */
  public HashMap<CIdExpression, PInterval> cloneTM(HashMap<CIdExpression, PInterval> toClone) {
    HashMap<CIdExpression, PInterval> temp = new HashMap<>();
    for (Entry<CIdExpression, PInterval> entry : toClone.entrySet()) {
      temp.put(entry.getKey(), entry.getValue());
    }
    return temp;
  }

  // ============Min-EntropyCalculation_BEGIN==================

  // the following section is for the min-entropy calculation. Decomment it to use ut
  /*
  /**
   * Calculates the Min-Entropy in this state. It uses the Information of the DependencyTracker for
   * the classes ("high" and "low") of the variables. The Min-Entropy is like: "How much Information
   * can I display with all "low" variables?" (e.g var vlow has the Interval [0,7]. It can express 3
   * Bit of information. If vlow is dependent on a "high" variable 3 Bit Entropy are subtracted from
   * the initially entropy of the "high" variable).
   *
   * @param mapping The mapping of the allowed Minimum Min-Entropy values
   * @param depMap the mapping of the dependencies of the individual variables
   * @param imap the mapping of the standard intervals
   * @param prec the mapping of high and low
   */
  /*
  public void calculateMinEntropy(
      MultiIntervalMinMaxMapping mapping,
      TreeMap<Variable, SortedSet<Variable>> depMap,
      TreeMap<Variable, IntervalExt> imap,
      DepPrecision prec) {
    // TreeMap<Variable, Double> minE = new TreeMap<>();

    // We need:

    // allowed remaining Entropy of vars         <-- Done! (mapping)
    // dependencies to confidential variables    <-- Done ! (tM)
    // their size                                <-- Done! (size())

    // calculate minEntropy

    // create map for initial Entropy values
    hMap = new HashMap<>();
    minimax = mapping;

    for (Entry<Variable, SortedSet<Variable>> ent : depMap.entrySet()) {
      if (mapping.getMinMinEntMap().containsKey(ent.getKey())) {
        hMap.put(ent.getKey(), Math.log(imap.get(ent.getKey()).size().doubleValue()) / Math.log(2));
      }
    }
    //   Log.Log2(depMap);
    //    Log.Log2(hMap);

    for (Entry<Variable, SortedSet<Variable>> ent : depMap.entrySet()) {
      // the currenty handled variable
      Variable curvar = ent.getKey();

      //      Log.Log2(curvar + " viol " + prec.isViolable(curvar));

      // if curvar is a low Variable then check if it depends on a high variable. If so subtract the
      // bits displayable by the low from the initial Entropy of the high variable
      if (prec.isViolable(curvar)) {
        SortedSet<Variable> deps = ent.getValue();
        deps.remove(curvar);
        if (!deps.isEmpty()) {
          for (Variable high : deps) {
            //            Log.Log2(
            //                "intervals: " + intervals + " deps: " + deps + " high: " + high + "cur
            // " + curvar);
            //            Log.Log2("Intervals.gethigh" + intervals.get(high));

            // is a high variable;)
            if (!prec.isViolable(high)) {
              hMap.put(
                  high,
                  Math.max(
                      hMap.get(high)
                          - Math.log(ranges.get(curvar).size().doubleValue()) / Math.log(2),
                      0));
            }
          }
        }
      }
    }
    // Log.Log2(hMap);

    // sendMessage to this state.
  }
  */
  // ============Min-EntropyCalculation_END==================

  @Override
  public boolean checkProperty(String property) throws InvalidQueryException {
    if (intervalsOnly) {
      return false;
    }
    // Do an Min-EntropyCheck
    Log.Log2("FILE:" + property);
    if (property.equals("MinEntropyCheck")) {
      Log.Log2("FILE:");
      // minmapping <-- Map for Min-Entropy
      // return true for Error;
      // Map for comparison

      // Saving current results to File
      // ================================================================================
      String outputPath = "";
      try {
        outputPath = new java.io.File(".").getCanonicalPath();
      } catch (IOException e) {
        e.printStackTrace();
      }
      outputPath = outputPath + "\\output";
      File entropyResultFile = new File(outputPath + "\\EntropyResults.txt");
      if (entropyResultFile.exists()) {
        entropyResultFile.delete();
      }
      try {
        Log.Log2("FILE:");
        entropyResultFile.createNewFile();
      } catch (IOException e) {
        e.printStackTrace();
      }

      StringBuilder sb = new StringBuilder();
      sb.append(
          "This File is created when the analysis stops and the Min-entropy was calculated. The CPAchecker stops its analysis if it finds a violation. So if this happens without getting to the end of the analyis the intervals might be inaccurate. \nFor a pure Intervalanalysis start with min remaining min-entropy = 0. \n \n");
      sb.append("Ranges: \n");
      for (Entry<CIdExpression, PInterval> entry : ranges.entrySet()) {
        sb.append(
            "Var:"
                + String.format("%-32s", entry.getKey().toString())
                + ",   Range: "
                + entry.getValue()
                + "\n");
      }


      if (hMap != null) {
        sb.append("\n");
        sb.append("MinEntropy: \n");
        for (CIdExpression v : hMap.keySet()) {
          sb.append(
              "Min-Entropy for "
                  + v
                  + " is: "
                  + hMap.get(v)
                  + " allowed is minimum "
                  + minimax.getMinMinEntMap().get(v)
                  + "\n");
        }
      }
      List<String> lines;
      lines = Arrays.asList(sb.toString());
      try {
        Files.write(
            Paths.get(entropyResultFile.getAbsolutePath()), lines, StandardOpenOption.APPEND);
      } catch (IOException e) {
        e.printStackTrace();
      }

      // ================================================================================

      // Violation check
      logger.logf(Level.FINER, "Checking property: %s", property);
      // Log.Log("===============Checking property:" + property + "================");
      TreeMap<String, Double> minminEnt = minimax.getMinMinEntMap();

      boolean violation = false;

      for (CIdExpression v : hMap.keySet()) {
        if (minminEnt.containsKey(v.getName()) && hMap.get(v) < minminEnt.get(v.getName())) {
          logger.logf(
              Level.FINE,
              "Min-Entropy of %s with  %f is lesser than the given minimum of Min-Entropy %f",
              v,
              hMap.get(v),
              minminEnt.get(v.getName()));

          violation = true;
        }
      }

      return violation;
    }
    return false;
  }


}
