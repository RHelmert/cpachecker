

There could occur some errors related to not creating a state if there is an if-clause without an else clause. 
To avoid this, it is recommended that every if has at least an else{} part. Even if its empty

Following config files are used in this Analysis:
 - QIFC_ifc_hilo_Map.conf
 - QIFCIntervalMap.conf
 - QIFCMaxLoss.conf
 - quantPInterval.properties
 
 Specification:
 - qMultiInterval.spc
 
 Each config gives some information about how its used so this will be ommitted here. 
 
 
 Results of the Analysis can be found in output/EntropyResults.txt
 This includes the pIntervals and the min-entropy values.
 
IMPORTANT
   ================================================================================
   Known Bugs:
    - if we use nested while with a restriction on loopcount and this count is reached
     then the analysis will result in an endless loop. (This is because the innerloop
     resets the flag which determines if we should leave the loop)
     To solve this, we need a better tracking of loops (The problem is for !(x<y) we
     enter the loop with pTruthassumption = false. We need a better way to determine
  	 when a loop is entered or when not. The current way is to complex )
  	-(it's not a bug, it's a feature) The analysis is restricted to 32 Bit, because the number of values of a 64Bit variable cannot be displayed as a 64Bit variable(future rework with BigInteger planned). Nevertheless we let the analysis to calculate bigger pIntervals than 32Bit. In some rare cases this can lead to a truly unbound 64Bit variable for which the analysis can result in a wrong result. This will be automatically fixed, when 64Bit variables gets supported.
  	 
   ================================================================================