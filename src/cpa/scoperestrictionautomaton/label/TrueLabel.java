/**
 * 
 */
package cpa.scoperestrictionautomaton.label;

/**
 * @author holzera
 *
 * This label always returns true.
 */
public class TrueLabel<E> implements Label<E> {

  /* (non-Javadoc)
   * @see cpa.scoperestrictionautomaton.label.Label#matches(java.lang.Object)
   */
  @Override
  public boolean matches(E pE) {
    return true;
  }

}
