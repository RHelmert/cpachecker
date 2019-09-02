/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
 */
package org.sosy_lab.cpachecker.cpa.invariants.formula;

import static com.google.common.base.Preconditions.checkArgument;

import java.math.BigInteger;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import org.sosy_lab.cpachecker.cpa.invariants.CompoundInterval;
import org.sosy_lab.cpachecker.cpa.invariants.CompoundIntervalManager;
import org.sosy_lab.cpachecker.cpa.invariants.CompoundIntervalManagerFactory;
import org.sosy_lab.cpachecker.util.states.MemoryLocation;

public class Mod2AbstractionVisitor
    extends DefaultNumeralFormulaVisitor<CompoundInterval, Mod2AbstractionVisitor.Type> {

  public static enum Type {
    EVEN,

    ODD,

    UNKNOWN;
  }

  private final CompoundIntervalManagerFactory compoundIntervalManagerFactory;

  private final FormulaEvaluationVisitor<CompoundInterval> evaluationVisitor;

  private final Map<? extends MemoryLocation, ? extends NumeralFormula<CompoundInterval>>
      environment;

  private final Set<BooleanFormula<CompoundInterval>> assumptions;

  public Mod2AbstractionVisitor(
      CompoundIntervalManagerFactory pCompoundIntervalManagerFactory,
      FormulaEvaluationVisitor<CompoundInterval> pEvaluationVisitor,
      Map<? extends MemoryLocation, ? extends NumeralFormula<CompoundInterval>> pEnvironment,
      Set<BooleanFormula<CompoundInterval>> pAssumptions) {
    this.compoundIntervalManagerFactory = Objects.requireNonNull(pCompoundIntervalManagerFactory);
    this.evaluationVisitor = Objects.requireNonNull(pEvaluationVisitor);
    this.environment = Objects.requireNonNull(pEnvironment);
    this.assumptions = Objects.requireNonNull(pAssumptions);
  }

  @Override
  public Type visit(Add<CompoundInterval> pAdd) {
    Type op1Type = pAdd.getOperand1().accept(this);
    if (op1Type != Type.UNKNOWN) {
      Type op2Type = pAdd.getOperand2().accept(this);
      if (op2Type != Type.UNKNOWN) {
        if (op1Type == op2Type) {
          return Type.EVEN;
        }
        return Type.ODD;
      }
    }
    return visitDefault(pAdd);
  }

  @Override
  public Type visit(Multiply<CompoundInterval> pMultiply) {
    Type op1Type = pMultiply.getOperand1().accept(this);
    if (op1Type == Type.EVEN) {
      return Type.EVEN;
    }
    Type op2Type = pMultiply.getOperand2().accept(this);
    if (op2Type == Type.EVEN) {
      return Type.EVEN;
    }

    if (op1Type == Type.ODD) {
      if (op2Type == Type.ODD) {
        return Type.ODD;
      }
    }

    return visitDefault(pMultiply);
  }

  @Override
  public Type visit(Variable<CompoundInterval> pVariable) {
    NumeralFormula<CompoundInterval> value = environment.get(pVariable.getMemoryLocation());
    if (value != null) {
      Type t = value.accept(this);
      if (t != Type.UNKNOWN) {
        return t;
      }
    }
    return super.visit(pVariable);
  }

  @Override
  protected Type visitDefault(NumeralFormula<CompoundInterval> pFormula) {
    BooleanFormula<CompoundInterval> evenTemplate = instantiateModTemplate(pFormula, 2, 0);
    if (assumptions.contains(evenTemplate)) {
      return Type.EVEN;
    }
    BooleanFormula<CompoundInterval> oddTemplate = instantiateModTemplate(pFormula, 2, 1);
    if (assumptions.contains(oddTemplate)) {
      return Type.ODD;
    }

    CompoundIntervalManager compoundIntervalManager =
        compoundIntervalManagerFactory.createCompoundIntervalManager(pFormula.getTypeInfo());
    CompoundInterval value =
        InvariantsFormulaManager.INSTANCE
            .modulo(
                pFormula,
                InvariantsFormulaManager.INSTANCE.asConstant(
                    pFormula.getTypeInfo(), compoundIntervalManager.singleton(2)))
            .accept(evaluationVisitor, environment);
    if (value.isSingleton()) {
      if (value.contains(BigInteger.ZERO)) {
        return Type.EVEN;
      }
      return Type.ODD;
    }
    return Type.UNKNOWN;
  }

  private BooleanFormula<CompoundInterval> instantiateModTemplate(
      NumeralFormula<CompoundInterval> pDividend, int pDivisor, int pRemainder) {
    checkArgument(pDivisor >= 2, "Divisor must be greater than 1.");
    if (pRemainder < 0 || pRemainder >= pDivisor) {
      throw new IllegalArgumentException(
          String.format("The remainder must be between 0 and %d.", pDivisor - 1));
    }
    CompoundIntervalManager compoundIntervalManager =
        compoundIntervalManagerFactory.createCompoundIntervalManager(pDividend.getTypeInfo());
    BooleanFormula<CompoundInterval> hint =
        InvariantsFormulaManager.INSTANCE.equal(
            InvariantsFormulaManager.INSTANCE.modulo(
                pDividend,
                InvariantsFormulaManager.INSTANCE.asConstant(
                    pDividend.getTypeInfo(), compoundIntervalManager.singleton(pDivisor))),
            InvariantsFormulaManager.INSTANCE.asConstant(
                pDividend.getTypeInfo(), compoundIntervalManager.singleton(pRemainder)));
    return hint;
  }
}
