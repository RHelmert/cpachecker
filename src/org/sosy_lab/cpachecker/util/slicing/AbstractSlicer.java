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
package org.sosy_lab.cpachecker.util.slicing;

import java.util.Collection;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.core.Specification;

/**
 * Abstract implementation of {@link Slicer} that takes care of mapping the specification to slicing
 * criteria.
 *
 * <p>Implements {@link #getSlice(CFA, Specification)} by mapping the specification to a set of
 * target edges that are handed to {@link #getSlice(CFA, Collection)} as slicing criteria.
 */
public abstract class AbstractSlicer implements Slicer {

  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;
  private final SlicingCriteriaExtractor extractor;

  protected AbstractSlicer(
      SlicingCriteriaExtractor pExtractor, LogManager pLogger, ShutdownNotifier pShutdownNotifier) {
    extractor = pExtractor;
    logger = pLogger;
    shutdownNotifier = pShutdownNotifier;
  }

  @Override
  public Slice getSlice(CFA pCfa, Specification pSpecification) throws InterruptedException {

    Set<CFAEdge> slicingCriteria =
        extractor.getSlicingCriteria(pCfa, pSpecification, shutdownNotifier, logger);

    return getSlice(pCfa, slicingCriteria);
  }
}
