/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2014  Dirk Beyer
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
package org.sosy_lab.cpachecker.util.predicates.pathformula;

import java.io.PrintStream;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCFAEdgeException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;
import org.sosy_lab.cpachecker.util.Pair;
import org.sosy_lab.cpachecker.util.predicates.pathformula.pointeraliasing.PointerTargetSet;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;

public interface PathFormulaManager {

  PathFormula makeEmptyPathFormula();

  PathFormula makeEmptyPathFormula(PathFormula oldFormula);

  /**
   * Creates a new path formula representing an OR of the two arguments. Differently from {@link
   * BooleanFormulaManager#or(BooleanFormula, BooleanFormula)}, it also merges the SSA maps and
   * creates the necessary adjustments to the formulas if the two SSA maps contain different values
   * for the same variables.
   *
   * @param pF1 a PathFormula
   * @param pF2 a PathFormula
   * @return (pF1 | pF2)
   */
  PathFormula makeOr(PathFormula pF1, PathFormula pF2) throws InterruptedException;

  PathFormula makeAnd(PathFormula pPathFormula, BooleanFormula pOtherFormula);

  PathFormula makeAnd(PathFormula pPathFormula, CExpression pAssumption)
      throws CPATransferException, InterruptedException;

  PathFormula makeAnd(PathFormula oldFormula, CFAEdge edge) throws CPATransferException, InterruptedException;

  Pair<PathFormula, ErrorConditions> makeAndWithErrorConditions(PathFormula oldFormula, CFAEdge edge) throws CPATransferException, InterruptedException;

  /**
   * Create a copy of a PathFormula but with the given SSAMap. Note that this is almost always the
   * wrong method to call: if you need to use a specific SSAMap, you probably also need to use a
   * specific PointerTargetSet! So better call {@link #makeNewPathFormula(PathFormula, SSAMap,
   * PointerTargetSet)}.
   */
  @Deprecated
  PathFormula makeNewPathFormula(PathFormula pOldFormula, SSAMap pM);

  PathFormula makeNewPathFormula(PathFormula pOldFormula, SSAMap pM, PointerTargetSet pPts);

  PathFormula makeFormulaForPath(List<CFAEdge> pPath) throws CPATransferException, InterruptedException;

  /**
   * Takes a variable name and its type to create the corresponding formula out of it. The <code>
   * pContext</code> is used to supply this method with the necessary {@link SSAMap} and (if
   * necessary) the {@link PointerTargetSet}. The variable is assumed not to be a function
   * parameter, i.e. array won't be treated as pointer variable, but as a constant representing
   * starting address of the array.
   *
   * @param pContext the context in which the variable should be created
   * @param pVarName the name of the variable
   * @param pType the type of the variable
   * @return the created formula, which is always <b>instantiated</b>
   */
  Formula makeFormulaForVariable(PathFormula pContext, String pVarName, CType pType);

  /**
   * Takes a variable name and its type to create the corresponding formula out of it, without
   * adding SSA indices. The <code>pContextPTS</code> is used to supply this method with the
   * necessary {@link PointerTargetSet} for creating appropriate pointer variables. The variable is
   * assumed not to be a function parameter, i.e. array won't be treated as pointer variable, but as
   * a constant representing starting address of the array.
   *
   * @param pVarName the name of the variable
   * @param pType the type of the variable
   * @param pContextPTS the context in which the variable should be created
   * @param forcePointerDereference force the formula to make a pointer dereference (e.g. *UF
   *     main:x)
   * @return the created formula, which is always <b>instantiated</b>
   */
  Formula makeFormulaForUninstantiatedVariable(
      String pVarName, CType pType, PointerTargetSet pContextPTS, boolean forcePointerDereference);

  /**
   * Build a formula containing a predicate for all branching situations in the ARG. If a satisfying
   * assignment is created for this formula, it can be used to find out which paths in the ARG are
   * feasible.
   *
   * <p>This method may be called with an empty set, in which case it does nothing and returns the
   * formula "true".
   *
   * @param pElementsOnPath The ARG states that should be considered.
   * @return A formula containing a predicate for each branching.
   */
  BooleanFormula buildBranchingFormula(Set<ARGState> pElementsOnPath)
      throws CPATransferException, InterruptedException;

  /**
   * Build a formula containing a predicate for all branching situations in the
   * ARG. If a satisfying assignment is created for this formula, it can be used
   * to find out which paths in the ARG are feasible.
   *
   * This method may be called with an empty set, in which case it does nothing
   * and returns the formula "true".
   *
   * @param elementsOnPath The ARG states that should be considered.
   * @param parentFormulasOnPath TODO.
   * @return A formula containing a predicate for each branching.
   */
  BooleanFormula buildBranchingFormula(
      Set<ARGState> elementsOnPath,
      Map<Pair<ARGState, CFAEdge>, PathFormula> parentFormulasOnPath)
      throws CPATransferException, InterruptedException;

  /**
   * Extract the information about the branching predicates created by
   * {@link #buildBranchingFormula(Set)} from a satisfying assignment.
   *
   * A map is created that stores for each ARGState (using its element id as
   * the map key) which edge was taken (the positive or the negated one).
   *
   * @param pModel A satisfying assignment that should contain values for branching predicates.
   * @return A map from ARG state id to a boolean value indicating direction.
   */
  Map<Integer, Boolean> getBranchingPredicateValuesFromModel(Iterable<ValueAssignment> pModel);

  /**
   * Clear all internal caches.
   * Some launches are so huge, that may lead to memory limit,
   * so, in some case it ise useful to reset outdated (and, maybe, necessary) information
   */
  void clearCaches();

  /**
   * Convert a simple C expression to a formula consistent with the
   * current state of the {@code pFormula}.
   *
   * @param pFormula Current {@link PathFormula}.
   * @param expr Expression to convert.
   * @param edge Reference edge, used for log messages only.
   * @return Created formula.
   */
  Formula expressionToFormula(PathFormula pFormula, CIdExpression expr, CFAEdge edge)
      throws UnrecognizedCodeException;

  /**
   * Builds test for PCC that pF1 is covered by more abstract path formula pF2.
   * Assumes that the SSA indices of pF1 are smaller or equal than those of pF2.
   * Since pF1 may be merged with other path formulas resulting in pF2, needs to
   * add assumptions about the connection between indexed variables as included by
   * {@link PathFormulaManager#makeOr(PathFormula, PathFormula)}. Returns negation of
   * implication to check if it is unsatisfiable (implication is valid).
   *
   * @param pF1 path formula which should be covered
   * @param pF2 path formula which covers
   * @return pF1.getFormula() and assumptions and not pF2.getFormula()
   */
  BooleanFormula buildImplicationTestAsUnsat(PathFormula pF1, PathFormula pF2) throws InterruptedException;

  /**
   * Prints some information about the PathFormulaManager.
   */
  void printStatistics(PrintStream out);

  BooleanFormula addBitwiseAxiomsIfNeeded(
      BooleanFormula pMainFormula,
      BooleanFormula pEsxtractionFormula);

  PathFormulaBuilder createNewPathFormulaBuilder();

  /**
   * Builds a weakest precondition for the given edge and the postcondition
   *
   * @param pEdge Edge containing the statement for the precondition to be built
   * @param pPostcond Postcondition
   * @return Created precondition
   */
  BooleanFormula buildWeakestPrecondition(CFAEdge pEdge, BooleanFormula pPostcond)
      throws UnrecognizedCFAEdgeException, UnrecognizedCodeException, InterruptedException;

  PointerTargetSet
      mergePts(PointerTargetSet pPts1, PointerTargetSet pPts2, SSAMap pSSA)
          throws InterruptedException;
}
