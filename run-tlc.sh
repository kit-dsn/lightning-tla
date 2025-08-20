#!/bin/sh

# C1: Payment from user A to user B
exec java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC SpecificationIIatoIIIa.toolbox/RefinementA3/MC.tla -workers auto -deadlock
# C2: Payment from user A over user B to user C
exec java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC SpecificationIIatoIIIa.toolbox/RefinementA3ToC/MC.tla -workers auto -deadlock
# C3: Payment from user C over user A and user B to user D
exec java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC SpecificationIIatoIIIa.toolbox/RefinementCToD/MC.tla -workers auto -deadlock
# C4: Two payments: Payment from user A to user B and payment
exec java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC SpecificationIIatoIIIa.toolbox/RefinementA5B3/MC.tla -workers auto -deadlock
# C5: Two concurrent payments from user A to user B
exec java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC SpecificationIIatoIIIa.toolbox/RefinementA5A3/MC.tla -workers auto -deadlock

# Payment from user A over B to user C
exec java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC SpecificationIV.toolbox/MultiA3/MC.tla -workers auto -deadlock
# Two payments: Payment from user A over user B to user C and payment from user C over user B to user A
exec java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC SpecificationIV.toolbox/MultiA3C2/MC.tla -workers auto -deadlock
# Two concurrent payments: Payment from user A over user B to user C and payment from user A to user B
exec java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC SpecificationIV.toolbox/MultiA3A2/MC.tla -workers auto -deadlock
# Three payments: Payment from user A over B to C, payment from user B to A, and payment from user B to user C
exec java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC SpecificationIV.toolbox/MultiA3B1B1/MC.tla -workers auto -deadlock
# Payment from user A over user B, user C, and user D to user E
exec java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC SpecificationIV.toolbox/MultiAE3/MC.tla -workers auto -deadlock


# Verifying refinement I -> V in simulation mode
timeout 3h java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC -simulate SpecificationI.toolbox/RefineSpecV/MC.tla -workers auto -depth 300 -deadlock
# Verifying refinement I -> II in simulation mode
timeout 3h java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC -simulate SpecificationItoII.toolbox/RefineSpecII/MC.tla -workers auto -depth 300 -deadlock
# Verifying refinement II -> V in simulation mode
timeout 3h java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC -simulate SpecificationII.toolbox/Model/MC.tla -workers auto -depth 300 -deadlock
# Verifying refinement II -> III in simulation mode
timeout 3h java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC -simulate SpecificationIItoIII.toolbox/RefineSpecIII/MC.tla -workers auto -depth 300 -deadlock
# Verifying refinement III -> V in simulation mode
timeout 3h java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC -simulate SpecificationIII.toolbox/Model/MC.tla -workers auto -depth 300 -deadlock
# Verifying refinement III -> IV in simulation mode
timeout 3h java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC -simulate SpecificationIIItoIV.toolbox/RefineSpecIV/MC.tla -workers auto -depth 300 -deadlock
# Verifying refinement IV -> V in simulation mode
timeout 3h java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC -simulate SpecificationIV.toolbox/Model/MC.tla -workers auto -depth 300 -deadlock
# Verifying refinement IIa -> IIIa in simulation mode
timeout 3h java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC -simulate SpecificationIIatoIIIa.toolbox/RefineSpecIIIa/MC.tla -workers auto -depth 300 -deadlock
# Verifying refinement II -> IIa in simulation mode
timeout 3h java $JAVA_OPTS -cp tla2tools.jar tlc2.TLC -simulate SpecificationIItoIIa.toolbox/RefineSpecIIa/MC.tla -workers auto -depth 300 -deadlock
