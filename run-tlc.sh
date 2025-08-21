#!/bin/sh

OUTPUT_DIR="output"

TLA2TOOLS="/tlaplus/tla2tools.jar"
if [ $# -eq 2 ]; then
    TLA2TOOLS="$2"
fi

LEVEL=1
case "$1" in
    --smoke-test)
        LEVEL=0
        ;;
    --brief)
        LEVEL=1
        ;;
    --medium)
        LEVEL=2
        ;;
    --long)
        LEVEL=3
        ;;
    --all)
        LEVEL=4
        ;;
    *)
        echo "Usage: $0 <{--smoke-test | --brief | --medium | --long | --all}> [path to tla2tools]"
        exit 1
        ;;
esac

# MEMORY: If a model checking job fails because memory did not suffice, make more memory available
# by adding the paramter -Xmx. E.g. -Xmx72G for making 72 GB of RAM available.
DEFAULT_JAVA_OPTS="-XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC"
if [ -z "$JAVA_OPTS" ]; then
  JAVA_OPTS="$DEFAULT_JAVA_OPTS"
fi
	
check_model_checking_success() {
    local type="$1"
    echo ""
    echo "-----------------"
    echo ""
    grep "Model checking completed. No error has been found" $OUTPUT_DIR/$type.log > /dev/null && \
    	echo "Successfully checked $type." && \
    	return 0
    echo "$type Check failed."
    return 1
}

mkdir -p $OUTPUT_DIR

if [ "$LEVEL" -eq 0 ]; then
	echo "Just a smoke test that does not check anything useful."
	exec java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC SpecificationI.toolbox/SmokeTest/MC.tla -workers auto -deadlock | tee $OUTPUT_DIR/smoke_test.log
	check_model_checking_success "smoke_test"
fi

if [ "$LEVEL" -ge 1 ]; then
	echo "Model checking C1: Payment from user A to user B"
	exec java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC SpecificationIIatoIIIa.toolbox/RefinementA3/MC.tla -workers auto -deadlock | tee $OUTPUT_DIR/C1.log
	check_model_checking_success "C1"

	echo "Model checking C2: Payment from user A over user B to user C"
	exec java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC SpecificationIIatoIIIa.toolbox/RefinementA3ToC/MC.tla -workers auto -deadlock | tee $OUTPUT_DIR/C2.log
	check_model_checking_success "C2"

	echo "Model checking C3: Payment from user C over user A and user B to user D"
	exec java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC SpecificationIIatoIIIa.toolbox/RefinementCToD/MC.tla -workers auto -deadlock | tee $OUTPUT_DIR/C3.log
	check_model_checking_success "C3"

	if [ "$LEVEL" -ge 3 ]; then
		echo "Model checking C4: Two payments: Payment from user A to user B and payment"
		exec java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC SpecificationIIatoIIIa.toolbox/RefinementA5B3/MC.tla -workers auto -deadlock | tee $OUTPUT_DIR/C4.log
		check_model_checking_success "C4"

		if [ "$LEVEL" -ge 4 ]; then
			echo "Model checking C5: Two concurrent payments from user A to user B"
			exec java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC SpecificationIIatoIIIa.toolbox/RefinementA5A3/MC.tla -workers auto -deadlock | tee $OUTPUT_DIR/C5.log
			check_model_checking_success "C5"
		fi
	fi

	echo "Model checking M1: Payment from user A over B to user C"
	exec java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC SpecificationIV.toolbox/MultiA3/MC.tla -workers auto -deadlock | tee $OUTPUT_DIR/M1.log
	check_model_checking_success "M1"

	if [ "$LEVEL" -ge 2 ]; then
		echo "Model checking M2: Two payments: Payment from user A over user B to user C and payment from user C over user B to user A"
		exec java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC SpecificationIV.toolbox/MultiA3C2/MC.tla -workers auto -deadlock | tee $OUTPUT_DIR/M2.log
		check_model_checking_success "M2"

		echo "Model checking M3: Two concurrent payments: Payment from user A over user B to user C and payment from user A to user B"
		exec java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC SpecificationIV.toolbox/MultiA3A2/MC.tla -workers auto -deadlock | tee $OUTPUT_DIR/M3.log
		check_model_checking_success "M3"
	fi

	if [ "$LEVEL" -ge 3 ]; then
		echo "Model checking M4: Three payments: Payment from user A over B to C, payment from user B to A, and payment from user B to user C"
		exec java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC SpecificationIV.toolbox/MultiA3B1B1/MC.tla -workers auto -deadlock | tee $OUTPUT_DIR/M4.log
		check_model_checking_success "M4"

		echo "Model checking M5: Payment from user A over user B, user C, and user D to user E"
		exec java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC SpecificationIV.toolbox/MultiAE3/MC.tla -workers auto -deadlock | tee $OUTPUT_DIR/M5.log
		check_model_checking_success "M5"
	fi

	if [ "$LEVEL" -ge 3 ]; then
		echo "Checking refinement I -> V in simulation mode for one hour"
		timeout 1h java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC -simulate SpecificationI.toolbox/RefineSpecV/MC.tla -workers auto -depth 300 -deadlock | tee $OUTPUT_DIR/S1.log
		tail -n 1 $OUTPUT_DIR/S1.log | grep "states checked" > /dev/null && echo "---------" && echo "Check was successful."

		echo "Checking refinement I -> II in simulation mode for one hour"
		timeout 1h java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC -simulate SpecificationItoII.toolbox/RefineSpecII/MC.tla -workers auto -depth 300 -deadlock | tee $OUTPUT_DIR/S2.log
		tail -n 1 $OUTPUT_DIR/S2.log | grep "states checked" > /dev/null && echo "---------" && echo "Check was successful."

		echo "Checking refinement II -> V in simulation mode for one hour"
		timeout 1h java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC -simulate SpecificationII.toolbox/Model/MC.tla -workers auto -depth 300 -deadlock | tee $OUTPUT_DIR/S3.log
		tail -n 1 $OUTPUT_DIR/S3.log | grep "states checked" > /dev/null && echo "---------" && echo "Check was successful."

		echo "Checking refinement II -> III in simulation mode for one hour"
		timeout 1h java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC -simulate SpecificationIItoIII.toolbox/RefineSpecIII/MC.tla -workers auto -depth 300 -deadlock | tee $OUTPUT_DIR/S4.log
		tail -n 1 $OUTPUT_DIR/S4.log | grep "states checked" > /dev/null && echo "---------" && echo "Check was successful."

		echo "Checking refinement III -> V in simulation mode for one hour"
		timeout 1h java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC -simulate SpecificationIII.toolbox/Model/MC.tla -workers auto -depth 300 -deadlock | tee $OUTPUT_DIR/S5.log
		tail -n 1 $OUTPUT_DIR/S5.log | grep "states checked" > /dev/null && echo "---------" && echo "Check was successful."

		echo "Checking refinement III -> IV in simulation mode for one hour"
		timeout 1h java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC -simulate SpecificationIIItoIV.toolbox/RefineSpecIV/MC.tla -workers auto -depth 300 -deadlock | tee $OUTPUT_DIR/S6.log
		tail -n 1 $OUTPUT_DIR/S6.log | grep "states checked" > /dev/null && echo "---------" && echo "Check was successful."

		echo "Checking refinement IV -> V in simulation mode for one hour"
		timeout 1h java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC -simulate SpecificationIV.toolbox/Model/MC.tla -workers auto -depth 300 -deadlock | tee $OUTPUT_DIR/S7.log
		tail -n 1 $OUTPUT_DIR/S7.log | grep "states checked" > /dev/null && echo "---------" && echo "Check was successful."

		echo "Checking refinement IIa -> IIIa in simulation mode for one hour"
		timeout 1h java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC -simulate SpecificationIIatoIIIa.toolbox/RefineSpecIIIa/MC.tla -workers auto -depth 300 -deadlock | tee $OUTPUT_DIR/S8.log
		tail -n 1 $OUTPUT_DIR/S8.log | grep "states checked" > /dev/null && echo "---------" && echo "Check was successful."

		echo "Checking refinement II -> IIa in simulation mode for one hour"
		timeout 1h java $JAVA_OPTS -cp $TLA2TOOLS tlc2.TLC -simulate SpecificationIItoIIa.toolbox/RefineSpecIIa/MC.tla -workers auto -depth 300 -deadlock | tee $OUTPUT_DIR/S9.log
		tail -n 1 $OUTPUT_DIR/S9.log | grep "states checked" > /dev/null && echo "---------" && echo "Check was successful."
	fi
fi