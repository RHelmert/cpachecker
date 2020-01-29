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
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.cpa.qMultiInterval;

import java.math.BigInteger;
import java.util.NavigableSet;
import java.util.Objects;
import java.util.TreeSet;


/**
 * This class is based the Interval class from package org.sosy_lab.cpachecker.cpa.interval. It
 * first was an extension. But since the other Intervalclass got finalized this one is a collection
 * of the methods which are important for the analysis
 */
public class IntervalExt implements Comparable<IntervalExt> {

  /**
   * the lower bound of the interval
   */
  private final Long low;

  /**
   * the upper bound of the interval
   */
  private final Long high;


  protected static final IntervalExt EMPTY = new IntervalExt(null, null);
  public static final IntervalExt UNBOUND = new IntervalExt(Long.MIN_VALUE, Long.MAX_VALUE);
  public static final IntervalExt BOOLEAN_INTERVAL = new IntervalExt(0L, 1L);
  public static final IntervalExt ZERO = new IntervalExt(0L, 0L);
  public static final IntervalExt ONE = new IntervalExt(1L, 1L);

  /**
   * Constructor for a Interval with a single value e.g IntervalExt(2L) --> [2,2]
   *
   * @param pValue Long value for low AND high limit
   */
  public IntervalExt(Long pValue) {
    low = pValue;
    high = pValue;

  }
  /**
   * Constructor for a Interval two values e.g IntervalExt(2L,10L) --> [2,10]
   *
   * @param low low limit of the interval
   * @param high high limit of the interval
   */
  public IntervalExt(Long low, Long high) {

    if ((low == null) != (high == null)) {
      throw new IllegalStateException("Interval: [" + low + "," + high + "]");
    }

    if (low != null && high != null && low > high) {
      throw new IllegalStateException("Interval: [" + low + "," + high + "]");
    }

    this.low = low;
    this.high = high;
  }


  public Long getLow() {
    return low;
  }

  public Long getHigh() {
    return high;
  }

  /**
   * adds two intervals with overflow handling
   *
   * @param interval interval to add
   * @return resulting interval
   */
  public IntervalExt plus(IntervalExt interval) {
    if (isEmpty() || interval.isEmpty()) {
      return EMPTY;
    }

    return new IntervalExt(scalarPlus(low, interval.low), scalarPlus(high, interval.high));
  }

  @Override
  public String toString() {
    return "[" + low + "," + high + "]";
  }
  /**
   * This method determines whether the interval is empty or not.
   *
   * @return true, if the interval is empty, i.e. the lower and upper bounds are null
   */
  public boolean isEmpty() {
    return low == null && high == null;
  }
  /**
   * This method adds two scalar values and returns their sum, or on overflow Long.MAX_VALUE or
   * Long.MIN_VALUE, respectively.
   *
   * @param x the first scalar operand
   * @param y the second scalar operand
   * @return the sum of the first and second scalar operand or on overflow Long.MAX_VALUE and
   *     Long.MIN_VALUE, respectively.
   */
  private static Long scalarPlus(Long x, Long y) {
    Long result = x + y;

    // both operands are positive but the result is negative
    if ((Long.signum(x) + Long.signum(y) == 2) && Long.signum(result) == -1) {
      result = Long.MAX_VALUE;
    } else if ((Long.signum(x) + Long.signum(y) == -2) && Long.signum(result) == +1) {
      result = Long.MIN_VALUE;
    }

    return result;
  }

  /**
   * This method negates this interval.
   *
   * @return new negated interval
   */
  public IntervalExt negate() {
    return new IntervalExt(scalarTimes(high, -1L), scalarTimes(low, -1L));
  }
  /**
   * This method multiplies two scalar values and returns their product, or on overflow
   * Long.MAX_VALUE or Long.MIN_VALUE, respectively.
   *
   * @param x the first scalar operand
   * @param y the second scalar operand
   * @return the product of the first and second scalar operand or on overflow Long.MAX_VALUE and
   *     Long.MIN_VALUE, respectively.
   */
  private static Long scalarTimes(Long x, Long y) {
    Long bound = (Long.signum(x) == Long.signum(y)) ? Long.MAX_VALUE : Long.MIN_VALUE;

    // if overflow occurs, return the respective bound
    if (x != 0 && ((y > 0 && y > (bound / x)) || (y < 0 && y < (bound / x)))) {
      return bound;
    } else {
      return x * y;
    }
  }

  /**
   * This method intersects two intervals see {@link Interval#intersect(Interval other) intersect}
   *
   * @param other interval which is intersected
   * @return the intersection of the both intervals
   */
  public IntervalExt intersect(IntervalExt other) {
    if (this.intersects(other)) {
      return new IntervalExt(Math.max(low, other.low), Math.min(high, other.high));
    } else {
      return EMPTY;
    }
  }
  /**
   * This method determines if this interval intersects with another interval.
   *
   * @param other the other interval
   * @return true if the intervals intersect, else false
   */
  public boolean intersects(IntervalExt other) {
    if (isEmpty() || other.isEmpty()) {
      return false;
    }

    return (low >= other.low && low <= other.high)
        || (high >= other.low && high <= other.high)
        || (low <= other.low && high >= other.high);
  }

  /**
   * This method applies the union operator on two intervals see {@link Interval#union(Interval
   * other) union}
   *
   * @param other interval
   * @return the union of the both intervals
   */
  public IntervalExt union(IntervalExt other) {
    if (isEmpty() || other.isEmpty()) {
      return EMPTY;
    } else if (low <= other.low && high >= other.high) {
      return this;
    } else if (low >= other.low && high <= other.high) {
      return other;
    } else {
      return new IntervalExt(Math.min(low, other.low), Math.max(high, other.high));
    }
  }

  /**
   * This method returns true if a number is contained in the interval
   *
   * @param number which could be contained
   * @return true if the number is contained else false
   */
  public boolean contains(int number) {
    return (number > getLow() && number < getHigh());
  }
  /**
   * This method determines if this interval contains another interval.
   *
   * <p>The method still returns true, if the borders match. An empty interval does not contain any
   * interval and is not contained in any interval either. So if the callee or parameter is an empty
   * interval, this method will return false.
   *
   * @param other the other interval
   * @return true if this interval contains the other interval, else false
   */
  public boolean contains(IntervalExt other) {
    return (!isEmpty() && !other.isEmpty() && low <= other.low && other.high <= high);
  }
  /**
   * This method determines if this interval is definitely greater than the other interval.
   *
   * @param other interval to compare with
   * @return true if the lower bound of this interval is always strictly greater than the upper
   *     bound of the other interval, else false
   */
  public boolean greaterThan(IntervalExt other) {
    return !isEmpty() && !other.isEmpty() && low > other.high;
  }

  /**
   * This method determines if this interval is definitely greater or equal than the other interval.
   * The equality is only satisfied for one single value!
   *
   * @param other interval to compare with
   * @return true if the lower bound of this interval is always strictly greater or equal than the
   *     upper bound of the other interval, else false
   */
  public boolean greaterOrEqualThan(IntervalExt other) {
    return !isEmpty() && !other.isEmpty() && low >= other.high;
  }

  /**
   * This method returns true if a number is contained in the interval
   *
   * @param number which could be contained
   * @return true if the number is contained else false
   */
  public boolean contains(long number) {
    return (number > getLow() && number < getHigh());
  }

  /**
   * This method returns the size of the Interval TODO if the interval is completely unbound the
   * size cannot be displayed as a long (maybe use BigInteger)
   *
   * @return the size of this interval
   */
  public BigInteger size() {
    if (isEmpty()) {
      return BigInteger.ZERO;
    }
    if (getLow() < Long.MIN_VALUE / 2 && getHigh() >= Long.MAX_VALUE / 2) {
      // throw new ArithmeticException();
      // assert false : "Completely unbound (64 Bit) intervals are currently not supported";
      return new BigInteger("" + Long.MAX_VALUE);
    }
    BigInteger res = new BigInteger("" + getHigh());
    res = res.subtract(new BigInteger("" + getLow()));
    res = res.add(BigInteger.ONE);

    return res;
  }

  @Override
  public int compareTo(IntervalExt obj) {

    if (this.equals(obj)) {
      return 0;
    }
    if ((this.getLow() < obj.getLow())
        || ((this.getLow().equals(obj.getLow())) && (this.getHigh() < obj.getHigh()))) {
      return -1;
    } else {
      return 1;
    }
  }

  /* (non-Javadoc)
   * @see java.lang.Object#equals(java.lang.Object)
   */
  @Override
  public boolean equals(Object other) {
    if (other != null && getClass().equals(other.getClass())) {
      IntervalExt another = (IntervalExt) other;
      return Objects.equals(low, another.low) && Objects.equals(high, another.high);
    }
    return false;
  }

  /* (non-Javadoc)
   * @see java.lang.Object#hashCode()
   */
  @Override
  public int hashCode() {
    return Objects.hash(low, high);
  }

  /**
   * This method allows to split one interval into two intervals. eg [1,10].split([5,6]) returns
   * [1,4],[7,10] This method maybe could also be used to cut off another interval from the current
   * one(not tested)
   *
   * @param other the splitting interval
   * @return one or two Intervals which is the original interval splitted. Alternatively and empty
   *     list if the parameter interval contains this interval.
   */
  public NavigableSet<IntervalExt> split(IntervalExt other) {
    // assert this.contains(other);

    TreeSet<IntervalExt> ts = new TreeSet<>();
    if (this.getLow() < other.getLow()) {
      ts.add(new IntervalExt(this.getLow(), other.getLow() - 1));
    }
    if (this.getHigh() > other.getHigh()) {
      ts.add(new IntervalExt(other.getHigh() + 1, this.getHigh()));
    }

    return ts;
  }


}
