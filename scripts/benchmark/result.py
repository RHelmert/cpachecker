"""
CPAchecker is a tool for configurable software verification.
This file is part of CPAchecker.

Copyright (C) 2007-2013  Dirk Beyer
All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.


CPAchecker web page:
  http://cpachecker.sosy-lab.org
"""

# prepare for Python 3
from __future__ import absolute_import, print_function, unicode_literals

from . import util

STR_TRUE = 'true'
STR_UNKNOWN = 'unknown'
STR_FALSE_LABEL = 'false(label)'
STR_FALSE_DEREF = 'false(valid-deref)'
STR_FALSE_FREE = 'false(valid-free)'
STR_FALSE_MEMTRACK = 'false(valid-memtrack)'

STR_LIST = [STR_TRUE, STR_UNKNOWN, STR_FALSE_LABEL, STR_FALSE_DEREF, STR_FALSE_FREE, STR_FALSE_MEMTRACK]

# string searched in filenames to determine correct or incorrect status.
# use lower case! the dict contains assignments 'filename' --> 'status'
PROP_SUBSTRINGS ={'_false-unreach-label': STR_FALSE_LABEL,
                  '_false-valid-deref':   STR_FALSE_DEREF,
                  '_false-valid-free':     STR_FALSE_FREE,
                  '_false-valid-memtrack': STR_FALSE_MEMTRACK
                  }

assert all('_false' in k for k in PROP_SUBSTRINGS.keys())

TRUE_SUBSTRINGS ={'.true.':                STR_TRUE,
                  '_true':                 STR_TRUE
                  }

# Score values taken from http://sv-comp.sosy-lab.org/
SCORE_CORRECT_TRUE = 2
SCORE_CORRECT_FALSE = 1
SCORE_UNKNOWN = 0
SCORE_WRONG_FALSE = -4
SCORE_WRONG_TRUE = -8

CATEGORY_UNKNOWN = ('', )

RESULT_CORRECT_TRUE = ('correct', STR_TRUE)
RESULT_CORRECT_FALSE_LABEL = ('correct', STR_FALSE_LABEL)
RESULT_CORRECT_FALSE_DEREF = ('correct', STR_FALSE_DEREF)
RESULT_CORRECT_FALSE_FREE = ('correct', STR_FALSE_FREE)
RESULT_CORRECT_FALSE_MEMTRACK = ('correct', STR_FALSE_MEMTRACK)

RESULT_UNKNOWN = ('unknown', )
RESULT_ERROR = ('error', )

RESULT_WRONG_TRUE = ('wrong', STR_TRUE)
RESULT_WRONG_FALSE_LABEL = ('wrong', STR_FALSE_LABEL)
RESULT_WRONG_FALSE_DEREF = ('wrong', STR_FALSE_DEREF)
RESULT_WRONG_FALSE_FREE = ('wrong', STR_FALSE_FREE)
RESULT_WRONG_FALSE_MEMTRACK = ('wrong', STR_FALSE_MEMTRACK)


def statusOfFile(filename):
    """
    This function returns the status of a file, 
    this is the property in the filename.
    """
    # first check PROP/FALSE, because it is a substring of PROP
    for key in PROP_SUBSTRINGS:
        if key in filename.lower():
            return PROP_SUBSTRINGS[key]
    return STR_TRUE # if no hint is given, assume TRUE


def fileIsFalse(filename):
    return util.containsAny(filename, PROP_SUBSTRINGS.keys())

def fileIsTrue(filename):
    return util.containsAny(filename, TRUE_SUBSTRINGS.keys())


def getResultCategory(filename, status):
    '''
    This function return a string
    that shows the relation between status and file.
    '''
    status = status.lower()

    # for backwards-compatibility of table-generator only
    if status == 'safe': status = STR_TRUE
    if status == 'unsafe': status = STR_FALSE_LABEL

    fileStatus = statusOfFile(filename)

    if status == fileStatus:
        prefix = 'correct'
    else:
        prefix = 'wrong'

    if status in [STR_FALSE_LABEL, STR_FALSE_DEREF, STR_FALSE_FREE, STR_FALSE_MEMTRACK, STR_TRUE]:
        return (prefix, status)
    elif status == STR_UNKNOWN:
        return RESULT_UNKNOWN
    else:
        return RESULT_ERROR


def calculateScore(category):
    return {RESULT_CORRECT_TRUE:   SCORE_CORRECT_TRUE,
            RESULT_WRONG_TRUE:     SCORE_WRONG_TRUE,
            RESULT_CORRECT_FALSE_LABEL:    SCORE_CORRECT_FALSE,
            RESULT_CORRECT_FALSE_DEREF:    SCORE_CORRECT_FALSE,
            RESULT_CORRECT_FALSE_FREE:     SCORE_CORRECT_FALSE,
            RESULT_CORRECT_FALSE_MEMTRACK: SCORE_CORRECT_FALSE,
            RESULT_WRONG_FALSE_LABEL:      SCORE_WRONG_FALSE,
            RESULT_WRONG_FALSE_DEREF:      SCORE_WRONG_FALSE,
            RESULT_WRONG_FALSE_FREE:       SCORE_WRONG_FALSE,
            RESULT_WRONG_FALSE_MEMTRACK:   SCORE_WRONG_FALSE,
            }.get(category,  SCORE_UNKNOWN)
