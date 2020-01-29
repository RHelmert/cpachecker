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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.TreeMap;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.c.CAssignment;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression.BinaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIntegerLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CRightHandSide;
import org.sosy_lab.cpachecker.cfa.ast.c.CStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CDeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionReturnEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CReturnStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.cfa.types.c.CPointerType;
import org.sosy_lab.cpachecker.core.defaults.ForwardingTransferRelation;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
// import org.sosy_lab.cpachecker.cpa.ifcsecurity.ControlDependencyTrackerState;
// import org.sosy_lab.cpachecker.cpa.ifcsecurity.DependencyTrackerState;
// import org.sosy_lab.cpachecker.cpa.ifcsecurity.dependencytracking.Variable;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;
import org.sosy_lab.cpachecker.util.LoopStructure;
import org.sosy_lab.cpachecker.util.LoopStructure.Loop;

public class MultiIntervalRelation
    extends ForwardingTransferRelation<MultiIntervalState, MultiIntervalState, Precision> {

  // ================================================================================
  // Vars
  // ================================================================================
  @SuppressWarnings("unused")
  private LogManager logger;

  private TreeMap<String, IntervalExt> imap;
  // only needed for min_Entropy calculation
  @SuppressWarnings("unused")
  private MultiIntervalMinMaxMapping minEnt;

  @SuppressWarnings("unused")
  private boolean intervalsOnly;

  LoopStructure loopStruct;
  ImmutableList<Loop> loops;
  ImmutableSet<CFANode> lheads;
  ImmutableSet<CFAEdge> innerEdges;

  // ================================================================================
  // Constructor
  // ================================================================================
  public MultiIntervalRelation(LogManager logger, IntervalMapping imap, CFA cfa) {
    this.logger = logger;
    // this.minEnt = minEnt;
    // this.intervalsOnly = intervalsOnly;
    this.imap = imap.getMap();
    loopStruct = cfa.getLoopStructure().get();
    loops = cfa.getLoopStructure().get().getAllLoops().asList();
    lheads = cfa.getLoopStructure().get().getAllLoopHeads();
    // Only Intervals will be calculated
    intervalsOnly = true;

    // the following line disables the log
    // Log.Disable();
  }

  // Constructor for min-Entropy calculation

  public MultiIntervalRelation(
      LogManager logger, IntervalMapping imap, MultiIntervalMinMaxMapping minEnt, CFA cfa) {
    this.logger = logger;
    this.minEnt = minEnt;
    this.imap = imap.getMap();
    loopStruct = cfa.getLoopStructure().get();
    loops = cfa.getLoopStructure().get().getAllLoops().asList();
    lheads = cfa.getLoopStructure().get().getAllLoopHeads();
    // Intervals and Min_Entropy wioll be calculated
    intervalsOnly = false;

    // the following line disables the log
    // Log.Disable();
  }

  // ================================================================================
  // Methods
  // ================================================================================

  //  // Calculate if the state is in an loop
  //  private boolean IsInnerloop(CFANode cNode) {
  //    for (Loop lop : loops) {
  //      if (lop.getLoopNodes().contains(cNode)) {
  //        return true;
  //      }
  //    }
  //    return false;
  //  }

  // Calculate if the state is a loophead
  /**
   * Calculates if the given state is a loophead in the program
   *
   * @param cNode the node to be tested
   * @return true if the state is a loophead, false if not
   */
  private boolean isLoopHead(CFANode cNode) {
    if (lheads.contains(cNode)) {
      return true;
    } else {
      return false;
    }
  }

  // Calculate if a loop is left
  /**
   * Calculates it the given edge is a leaving edge i.e it is an edge which leaves one (ore more)
   * arbitrary loops
   *
   * @param cEdge the edge to be tested
   * @return true if the edge is a loop-leaving edge
   */
  private boolean isLoopExit(CAssumeEdge cEdge) {
    for (Loop lop : loops) {
      if (lop.getOutgoingEdges().contains(cEdge)) {
        return true;
      }
    }
    return false;
  }

  // returns a set of Loops with this loophead
  //  private ImmutableSet<Loop> getLoopByHead(CFANode head) {
  //    Log.Log2("Head: "+ head +"Loops:"+loopStruct.getLoopsForLoopHead(head));
  //    return loopStruct.getLoopsForLoopHead(head);
  //  }

  // The following is another (not working atm) approach of returning all Variables of a loop. This
  // would be more precice because it should only return variables of the current loop and not the
  // inner one
  // so the one from the inner one, which already got approximated doesnt get approximated a second
  // time
  // example :

  // while (x < 10)
  // ____x = x+1;
  // ____v = v+10;
  // ____z = z+1
  // ____while (y <10){
  // ________y = y+1;
  // ________z = z*2;
  // ____}
  // }

  // the inner one approximates y to [10,UNBOUND] and z to [UNBOND,UNBOUND] since these variables
  // are in the body
  // the outer one approximates v,z,y to [UNBUOND,UNBOUND] and x to [10,UNBOUND] due to the
  // condition.
  // better would be v,z to [UNBOUND,UNBOUND] and x and y to [10,UNBOUND] since it is not possible
  // to leave the inner loop with a y value smaller than 10
  // this is what the following prototype method should do (but it is not working. It also needs a
  // proof.)

  //  /**
  //   * returns all Variables of this Loop. Only Variable which occur on the lhs of a statement
  // will be
  //   * returned
  //   *
  //   * @param cNode the Loophead
  //   * @return A set of Variables
  //   */
  //  private HashSet<Variable> getAllVarsOfThisLoop(CFANode cNode) {
  //    assert isLoopHead(cNode);
  //    HashSet<CFAEdge> edges = new HashSet<>();
  //    HashSet<Variable> vars = new HashSet<>();
  //    boolean headfound = false;
  //    // find all edges of this loop (the first for loop should run at most one time since every
  // state
  //    // can be loophead from at most one loop (or not?))
  //
  //    for (Loop lop : loops) {
  //      if (lop.getLoopHeads().contains(cNode)) {
  //        assert !headfound;
  //        edges.addAll(lop.getInnerLoopEdges());
  //
  //        //make a new Set of heads
  //        HashSet<CFANode> heads = new HashSet<>();
  //        heads.addAll(lop.getLoopHeads());
  //        //remove the head of the outer loop
  //        heads.remove(cNode);
  //        // now heads only has nodes of the inner loops left
  //        HashSet<Loop> innerloops = new HashSet<>();
  //        for (CFANode h : heads) {
  //          innerloops.addAll(getLoopByHead(h));
  //        }
  //        // now remove all edges of the inner loops
  //        for (Loop l : innerloops) {
  //          edges.removeAll(l.getInnerLoopEdges());
  //        }
  //        headfound = true;
  //      }
  //    }
  //
  //    // now remove all edges which are in an inner loop
  //
  //    // filter all statement edges
  //    for (CFAEdge e : edges) {
  //      if (e instanceof CStatementEdge
  //          && ((CStatementEdge) e).getStatement() instanceof CAssignment) {
  //        CExpression op1 = ((CAssignment) ((CStatementEdge) e).getStatement()).getLeftHandSide();
  //        vars.add(new Variable(((CIdExpression) op1).getDeclaration().getQualifiedName()));
  //      }
  //    }
  //
  //    return vars;
  //  }
  /**
   * returns all Variables of this Loop. Only Variable which occur on the lhs of a statement will be
   * returned. cNode needs to be a loophead. Else an assertion error is thrown.
   *
   * @param cNode the Loophead
   * @return All the Variables which occur on the lhs of some statement in the body of this loophead
   *     and andy inner loops.
   */
  private HashSet<CIdExpression> getAllVarsOfThisLoop(CFANode cNode) {
    assert isLoopHead(cNode);
    HashSet<CFAEdge> edges = new HashSet<>();
    HashSet<CIdExpression> vars = new HashSet<>();
    boolean headfound = false;
    // find all edges of this loop (the first for loop should run at most one time since every state
    // can be loophead from at most one loop (or not?))
    for (Loop lop : loops) {
      if (lop.getLoopHeads().contains(cNode)) {
        assert !headfound;
        edges.addAll(lop.getInnerLoopEdges());
        headfound = true;
        }
    }

    // filter all statement edges
    for (CFAEdge e : edges) {
      if (e instanceof CStatementEdge
          && ((CStatementEdge) e).getStatement() instanceof CAssignment) {
        CExpression op1 = ((CAssignment) ((CStatementEdge) e).getStatement()).getLeftHandSide();
        vars.add((CIdExpression) op1);
        }
      }

    return vars;
    }

  private BinaryOperator swapOp(BinaryOperator op) {
    assert op.isLogicalOperator();
    switch (op) {
      case LESS_EQUAL:
        return BinaryOperator.GREATER_EQUAL;
      case LESS_THAN:
        return BinaryOperator.GREATER_THAN;
      case GREATER_EQUAL:
        return BinaryOperator.LESS_EQUAL;
      case GREATER_THAN:
        return BinaryOperator.LESS_THAN;
      default:
        throw new AssertionError("Unknown binary operator");

    }
  }



  // ================================================================================
  // Edgehandling
  // ================================================================================
  @Override
  protected @Nullable MultiIntervalState handleAssumption(
      CAssumeEdge pCfaEdge, CExpression pExpression, boolean pTruthAssumption)
      throws CPATransferException {


    // clone old state
    MultiIntervalState st = state.clone();

    // we wont leave the loop ant the last state is a loophead. So we enter the loop
    if (!isLoopExit(pCfaEdge) && isLoopHead(pCfaEdge.getPredecessor())) {
      st.setInnterloop(true);
      st.addLoop(pCfaEdge.getPredecessor());
    }

    // if we are in LEAVING, that means the loopbound is reached in some state. We wont go in the
    // loop for another round
    if (isLoopHead(pCfaEdge.getPredecessor())
        && st.eS == MultiIntervalState.exitStatus.LEAVING
        && !isLoopExit(pCfaEdge)) {
      // throw new CPATransferException("Non existent Transfer");
      // Log.Log2("Return null");
      return null;
    }

    // Since we wont go in the loop for another round we have to leave the loop. Were setting every
    // Variable to unbound and the rest of the method will do the rest.
    if (isLoopHead(pCfaEdge.getPredecessor())
        && st.eS == MultiIntervalState.exitStatus.LEAVING
        && isLoopExit(pCfaEdge)) {

      HashMap<CIdExpression, PInterval> temp = new HashMap<>();
      HashSet<CIdExpression> unboundCandidates = getAllVarsOfThisLoop(pCfaEdge.getPredecessor());
      for (CIdExpression var : unboundCandidates) {
        st.removeKey(var);
        temp.put(var, PInterval.UNBOUND);
        //          Log.Log2("-----------------------------------------------");
      }


      st.combineMaps(temp);
      // if we are in an inner loop (loopc.size()>1) then we continue in Leaving mode
      // TODO Flag for executing the outer loop further.
      if (st.getLopC().size() > 1) {
        // Log.Log2("To an inner");
        st.eS = MultiIntervalState.exitStatus.LEAVING;
      } else {
        // Log.Log2("To outer");
        st.eS = MultiIntervalState.exitStatus.IDLE;
      }

      // Log.Log2("Exited after approximating");
    }

    // check if we are still in a loop if we just left a loop
    if (isLoopExit(pCfaEdge)) {
      // Were leaving so we remove the one were in
      st.resetLoop(pCfaEdge.getPredecessor());
      // Test if we're still in a loop
      if (!st.getLopC().isEmpty()) {
        // We left an inner loop
        // so we are still in a loop
        st.setInnterloop(true);
      } else {
        // Log.Log2("Vars removed");
        //        st.removeVars();
        // we left all loops and continue normal
        st.setInnterloop(false);
      }
    }

    // Now the real assumption edge handling
    BinaryOperator operator = ((CBinaryExpression) pExpression).getOperator();
    CExpression operand1 = ((CBinaryExpression) pExpression).getOperand1();
    CExpression operand2 = ((CBinaryExpression) pExpression).getOperand2();

    // swap the order of the operands if they are not in the right order
    // TODO the whole operand and expression evaluation can be reworked

    if (operand1 instanceof CIntegerLiteralExpression) {
      // Log.Log2("Swapped " + operand1 + " " + operator + " " + operand2 + " to");
      CExpression temp = operand1;
      operand1 = operand2;
      operand2 = temp;
      if (!(operator.equals(BinaryOperator.EQUALS) || operator.equals(BinaryOperator.NOT_EQUALS))) {
        operator = swapOp(operator);
      }
      // Log.Log2(operand1 + " " + operator + " " + operand2 + " .");
    }

    ExpressionValueRangeVisitor visitor = new ExpressionValueRangeVisitor(st, pCfaEdge);
    PInterval interval1 = operand1.accept(visitor);
    PInterval interval2 = operand2.accept(visitor);

    assert !interval1.isEmpty() : operand1;
    assert !interval2.isEmpty() : operand2;

    // we dont support full expressions for now
    assert operand1 instanceof CIdExpression : "This form is currently not supported" + operand1;
    assert (operand2 instanceof CIntegerLiteralExpression || operand2 instanceof CIdExpression)
        : "This form is currently not supported";

    // TODO work with qualified name!
    // even if the operand is just a constant this will work

    CIdExpression var1 = (CIdExpression) operand1;
    CIdExpression var2;
    if (operand2 instanceof CIdExpression) {
      var2 = (CIdExpression)operand2;
    } else {
      var2 = null;
    }


    // the following lines assume that one of the operands is an identifier
    // and the other one represented with an interval (example "x<[3;5]").
    // If none of the operands is an identifier, nothing is done.

    if (!pTruthAssumption) {
      operator = operator.getOppositLogicalOperator();
    }

    HashMap<CIdExpression, PInterval> temp = new HashMap<>();
    HashMap<CIdExpression, PInterval> tempOut = new HashMap<>();
    temp.put(var1, st.getRangeMap().get(var1));
    if (var2 != null) {
      temp.put(var2, st.getRangeMap().get(var2));
    }

    // TODO make operant2 always an Interval and let be operant 1 always a Variable.
    // TODO alternative for later: Swap operator1 or refactor it to like c+1 < d => _c_ < d-1
    // && _d_ > c+1 where _c_,_d_ is the variable for which the interval should be saved
    // then much more different assumption edges can be handled

    // this switch() is quite messy because of the autoformatting of the CPAchecker
    // now the assumption interval logic
    switch (operator) {
        // , a < const
      case LESS_THAN:
        {
          for (Entry<CIdExpression, PInterval> entry : temp.entrySet()) {
            if ((entry.getKey().equals(var1)
                && !entry.getValue().limitUpperBound(interval2.minus(1L)).isEmpty())) {
              tempOut.put(var1, interval1.limitUpperBound(interval2.minus(1L)));

            } else if (!(operand2 instanceof CIntegerLiteralExpression)
                && !entry.getValue().limitLowerBound(interval2.plus(1L)).isEmpty()
                && entry.getKey().equals(var2)) {
              tempOut.put(var2, interval2.limitLowerBound(interval1.plus(1L)));
            }
          }
          return returnState(st, var1, var2, tempOut);
        }
      case GREATER_THAN:
        {
          for (Entry<CIdExpression, PInterval> entry : temp.entrySet()) {
            if ((entry.getKey().equals(var1)
                && !entry.getValue().limitLowerBound(interval2.plus(1L)).isEmpty())) {

              tempOut.put(var1, interval1.limitLowerBound(interval2.plus(1L)));

            } else if (!(operand2 instanceof CIntegerLiteralExpression)
                && !entry.getValue().limitUpperBound(interval2.minus(1L)).isEmpty()
                && entry.getKey().equals(var2)) {
              tempOut.put(var2, interval2.limitUpperBound(interval1.minus(1L)));
            }
          }
          return returnState(st, var1, var2, tempOut);
        }

      case LESS_EQUAL:
        {
          for (Entry<CIdExpression, PInterval> entry : temp.entrySet()) {
            if ((entry.getKey().equals(var1)
                && !entry.getValue().limitUpperBound(interval2).isEmpty())) {
              tempOut.put(
                 var1,
                  interval1.limitUpperBound(interval2));

            } else if (!(operand2 instanceof CIntegerLiteralExpression)
                && !entry.getValue().limitLowerBound(interval2).isEmpty()
                && entry.getKey().equals(var2)) {
              tempOut.put(var2, interval2.limitLowerBound(interval1));
            }
          }
          return returnState(st, var1, var2, tempOut);
        }
      case GREATER_EQUAL:
        {
          for (Entry<CIdExpression, PInterval> entry : temp.entrySet()) {
            if ((entry.getKey().equals(var1)
                && !entry.getValue().limitLowerBound(interval2).isEmpty())) {
              tempOut.put(var1, interval1.limitLowerBound(interval2));

            } else if (!(operand2 instanceof CIntegerLiteralExpression)
                && !entry.getValue().limitUpperBound(interval2).isEmpty()
                && entry.getKey().equals(var2)) {
              tempOut.put(var2, interval2.limitUpperBound(interval1));
            }
          }
          return returnState(st, var1, var2, tempOut);
        }

        // equals and not equals needs to be refactored a bit
      case EQUALS:
        {
          // case of disjunct intervals?
          for (Entry<CIdExpression, PInterval> entry : temp.entrySet()) {
            if ((entry.getKey().equals(var1) && !entry.getValue().intersect(interval2).isEmpty())) {
              tempOut.put(var1, entry.getValue().intersect(interval2));
            }
            if ((!(operand2 instanceof CIntegerLiteralExpression))
                && (entry.getKey().equals(var2)
                    && !entry.getValue().intersect(interval1).isEmpty())) {
              tempOut.put(var2, entry.getValue().intersect(interval1));
            }
          }
          return returnState(st, var1, var2, tempOut);
        }
      case NOT_EQUALS:
        {
          if ((operand2 instanceof CIdExpression
                  && ((CIdExpression) operand1).getDeclaration().getQualifiedName()
                      == ((CIdExpression) operand2).getDeclaration().getQualifiedName())
              || interval1.equals(interval2) && interval1.size().equals(BigInteger.ONE)) {

            return null;

            // NO
            // throw new CPATransferException("No Sucessor");
          }

          for (Entry<CIdExpression, PInterval> entry : temp.entrySet()) {
            if ((entry.getKey().equals(var1) && interval2.size().equals(BigInteger.ONE))) {
              PInterval r = entry.getValue().clone();
              r.addOut(new IntervalExt(interval2.getLow(), interval2.getHigh()));
              tempOut.put(
                  var1, r);
            } else if ((entry.getKey().equals(var1) && !interval2.size().equals(BigInteger.ONE))) {

              tempOut.put(var1, entry.getValue());
            } else if ((!(operand2 instanceof CIntegerLiteralExpression))
                && (entry.getKey().equals(var2) && interval1.size().equals(BigInteger.ONE))) {
              PInterval r = entry.getValue().clone();
              r.addOut(new IntervalExt(interval1.getLow(), interval1.getHigh()));
              tempOut.put(
                  var2, r);
            } else if ((!(operand2 instanceof CIntegerLiteralExpression))
                && (entry.getKey().equals(var2) && !interval1.size().equals(BigInteger.ONE))) {

              tempOut.put(var2, entry.getValue());
            }
          }
          return returnState(st, var1, var2, tempOut);
        }
      default:
        throw new UnrecognizedCodeException(
            "unexpected operator in assumption", pCfaEdge, pExpression);
    }
  }
  /**
   * A delegation from the handleAssumeEdge. Because this has to be called in every swith case this
   * is delegated to this method instead. It replaces all currently used variables in the temporary
   * treeMap with their newer versions.
   *
   * @param st current state
   * @param var1 variable to remove
   * @param var2 variable to remove
   * @param tempMap new values of the removed variables
   * @return null if this state cant be reached (i.e both used variables would have an empty
   *     interval after this edge)and the modified state if it can be reached
   */
  private MultiIntervalState returnState(
      MultiIntervalState st,
      CIdExpression var1,
      CIdExpression var2,
      HashMap<CIdExpression, PInterval> tempMap) {

    if (tempMap.isEmpty()) {
      // Dead path
      return null;
    } else {
      // modify the state
      // remove old keys
      if (var1 != null) {
      st.removeKey(var1);
      }
      if (var2 != null) {
      st.removeKey(var2);
      }
      // insert new ones
      st.combineMaps(tempMap);
      return st;
    }
  }

  @Override
  protected MultiIntervalState handleFunctionCallEdge(
      CFunctionCallEdge pCfaEdge,
      List<CExpression> pArguments,
      List<CParameterDeclaration> pParameters,
      String pCalledFunctionName)
      throws CPATransferException {
    //  TODO implement functions
    // clone old state
    MultiIntervalState st = state.clone();
    return st;
  }

  @Override
  protected MultiIntervalState handleFunctionReturnEdge(
      CFunctionReturnEdge pCfaEdge,
      CFunctionSummaryEdge pFnkCall,
      CFunctionCall pSummaryExpr,
      String pCallerFunctionName)
      throws CPATransferException {
    //  TODO implement functions
    // clone old state
    MultiIntervalState st = state.clone();
    return st;
  }
  // =================================================

  @Override
  protected MultiIntervalState handleDeclarationEdge(CDeclarationEdge pCfaEdge, CDeclaration pDecl)
      throws CPATransferException {

    // clone old state
    MultiIntervalState st = state.clone();

    if (pCfaEdge.getDeclaration() instanceof CVariableDeclaration) {

      CVariableDeclaration decl = (CVariableDeclaration) pCfaEdge.getDeclaration();

      // ignore pointer variables
      if (decl.getType() instanceof CPointerType) {
        assert false : "No Pointer at the moment";
        return st;
      }

      // Set the interval to the one specified in the config
      IntervalExt interval;
      interval = imap.get(pCfaEdge.getDeclaration().getName());
      if (interval == null) {
        interval = IntervalExt.UNBOUND;
      }
      // add it to the interval list
      CIdExpression cid = new CIdExpression(pDecl.getFileLocation(), pDecl);
      st.addRange(cid, new PInterval(interval));
    }

    return st;
  }

  @Override
  protected MultiIntervalState handleStatementEdge(CStatementEdge pCfaEdge, CStatement pStatement)
      throws CPATransferException {
    // clone old state
    MultiIntervalState st = state.clone();

    // Assignment handling (what else?)
    if (pStatement instanceof CAssignment) {
      CAssignment assignExpression = (CAssignment) pStatement;
      CExpression op1 = assignExpression.getLeftHandSide();
      CRightHandSide op2 = assignExpression.getRightHandSide();

      CIdExpression var = (CIdExpression) op1;
      //      if (st.eS == MultiIntervalState.exitStatus.COLLECT) {
      //        collectible.add(var);
      //      }
      // Statements like  a =  (c+d*X)/Y have to be handled by the visitor
      PInterval interval = evaluateInterval(st, op2, pCfaEdge);

      st.addRange(var, interval);
    }
    return st;
  }

  /**
   * This method calculates the Range in this state given the old Intervals, and the expression.
   *
   * @param readableState the state with the old intervals
   * @param expression the expression which is evaluated on the intervals
   * @param cfaEdge additionally the edge, which is only used to give details if the
   *     UnrecognizedCCodeException is thrown
   * @return the calculated new Range
   * @throws UnrecognizedCodeException self explanatory
   */
  private PInterval evaluateInterval(
      MultiIntervalState readableState, CRightHandSide expression, CFAEdge cfaEdge)
      throws UnrecognizedCodeException {
    return expression.accept(new ExpressionValueRangeVisitor(readableState, cfaEdge));
  }

  @Override
  protected MultiIntervalState handleReturnStatementEdge(CReturnStatementEdge pCfaEdge)
      throws CPATransferException {
    // clone old state
    MultiIntervalState st = state.clone();
    return st;
  }

  @Override
  protected MultiIntervalState handleBlankEdge(BlankEdge pCfaEdge) {
    // clone old state
    MultiIntervalState st = state.clone();
    // check if the next state is a loopStart
    if (isLoopHead(pCfaEdge.getSuccessor())) {
      st.setLoopstart();
      st.setInnterloop(true);
      // now all the while edges (currently only while)
      if (pCfaEdge.getDescription().replaceAll("\n", " ") == "while") {
        // Log.Log2("incoming to" + pCfaEdge.getSuccessor());
        //        st.setLoopVars(getAllVarsOfThisLoop(pCfaEdge.getSuccessor()));
        Log.Log2(
            "Loopvars set on "
                + pCfaEdge.getSuccessor()
                + " vars"
                + getAllVarsOfThisLoop(pCfaEdge.getSuccessor()));
      }
    }

    // st.setDep(state.getDep());
    return st;
  }

  @Override
  protected MultiIntervalState handleFunctionSummaryEdge(CFunctionSummaryEdge pCfaEdge)
      throws CPATransferException {
    // clone old state
    MultiIntervalState st = state.clone();
    return st;
  }

  // ================================================================================
  // Strengthening
  // ================================================================================

  @Override
  public Collection<? extends AbstractState> strengthen(
      AbstractState pState,
      Iterable<AbstractState> pOtherStates,
      CFAEdge pCfaEdge,
      Precision pPrecision)
      throws CPATransferException, InterruptedException {

    assert pState instanceof MultiIntervalState;

    // IMPORTANT INFORMATION:
    // Strengthen does not get called on merged states. So if the last state is a merged state there
    // will be no strengthening
    // converting to right state
    MultiIntervalState state1 = (MultiIntervalState) pState;

    // Deprecated
    //    if (pCfaEdge.getSuccessor().isLoopStart()) {
    //      state1.setLoopstart();
    //    }

    // important check for bounding loops
    // cam maybe transferred to assumption handlyng
    // the if can only be true if the last state was as assumption edge
    if (state1.hasToExitNow() && state1.eS == MultiIntervalState.exitStatus.IDLE) {
      assert (pCfaEdge instanceof CAssumeEdge);
      state1.eS = MultiIntervalState.exitStatus.LEAVING;
    }

    // Deprecated
    //        if (((CAssumeEdge) pCfaEdge).getTruthAssumption()) {
    //          state1.eS = MultiIntervalState.exitStatus.COLLECT_T;
    //
    //        } else {
    //          state1.eS = MultiIntervalState.exitStatus.COLLECT_F;
    //
    //        }
    //      } else if (state1.eS == MultiIntervalState.exitStatus.EXIT) {
    //        // this is not needed any more, since we set the status to idle if we leave the loop
    //        // state1.eS = MultiIntervalState.exitStatus.IDLE;
    //      }

    // test if theres no match to ONE entry, so we just left the loop
    //      assert !(state1.getLopC().size() > rContexts.size() + 1);
    //      if (state1.getLopC().size() == rContexts.size() + 1) {
    //
    //        // We successfully left one loop
    //        // state1.SendMessage("JustLeftOneLoop");
    //        // Log.Log2("Left");
    //        Set<CFANode> temp = ((TreeMap<CFANode, Integer>) state1.getLopC().clone()).keySet();
    //        temp.removeAll(rContexts);
    //        state1.eS = MultiIntervalState.exitStatus.IDLE;
    //        assert !temp.isEmpty();
    //
    //        // just one iteration
    //        for (CFANode node : temp) {
    //          state1.resetLoop(node);
    //        }
    //      }

    // Entropy calculation
    // =========================Min-Entropy_BEGIN=====================================
    /*pyTrackerState depTState = null;

        for (AbstractState p : pOtherStates) {

          if (p instanceof ControlDependencyTrackerState) {
            contDepTState = (ControlDependencyTrackerState) p;
          } else if (p instanceof DependencyTrackerState) {
            depTState = (DependencyTrackerState) p;
          }
          // else if (p instanceof LocationState) {
          //        LS = (LocationState) p;
        }

        //  strengthenSaveIntervals(state1, IAS);

        // Calculate the Min-Entropy on the last state

        assert contDepTState != null : "The analysis ControlDependencyTracking needs to be run";
        Map<CFANode, SortedSet<Variable>> contexts = contDepTState.getContexts();
        SortedSet<CFANode> rContexts = new TreeSet<>();
        // now look if there is a Context and only look for Elements which have an unempty
        // context.
        for (Entry<CFANode, SortedSet<Variable>> ent : contexts.entrySet()) {
          if (!ent.getValue().isEmpty()) {
            rContexts.add(ent.getKey());
          }
        }

    // Test if the previous state is the loop start.
    // if (pCfaEdge.getPredecessor().isLoopStart()) {
    // Bounding checks

    // Test if we are in the inner loop
    //      for (CFANode cf : rContexts) {
    //        if (pCfaEdge.getPredecessor().equals(cf)) {
    //          // We are in the inner loop so we set the flags and add a loop
    //          state1.setInnterloop(true);
    //          state1.addLoop(cf);
    //
    //          // and already collect
    //          // --leave this loop at the next entry, because we are just collecting
    // which has
    // to be
    //          // caused by
    //          // another loop
    //
    //        }
    //      }
    // }

    if (!(pCfaEdge instanceof BlankEdge)) {

          state1.SendMessage(rContexts);
          // state1.setDep(rContexts);
        }

        // this is for calculating the Min-Entropy
        if (pCfaEdge.getSuccessor().getNumLeavingEdges() == 0) {
      // marking the state als LastState
      // ---> there is a better way with should be highlighted
      state1.SendMessage("LastState!");

      assert depTState != null : "The analysis DependencyTracking needs to be run";

          Map<Variable, SortedSet<Variable>> map = depTState.getDependencies();
          TreeMap<Variable, SortedSet<Variable>> tM = new TreeMap<>();
          tM.putAll(map);
      // state1.setLast();
      // Calculate the entropy
      state1.calculateMinEntropy(minEnt, tM, imap, depTState.getPrec());
        }
      }
      */
    // =========================Min-Entropy_END=====================================
    return Collections.singleton(state1);
  }

  // ================================================================================
  // Strengthen delegations
  // ================================================================================

  // ================================================================================
  // Additional Methods
  // ================================================================================

}
