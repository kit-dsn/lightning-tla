TLA+ Artifacts for "Security of the Lightning Network: Model Checking a Stepwise Refinement with TLA+"
======================================================================================================

This repository contains the TLA+ specification of Lightning, refinements, models, and TLC configurations that accompany the paper:

> **Security of the Lightning Network: Model Checking a Stepwise Refinement with TLA+.**  
> Matthias Grundmann, Hannes Hartenstein. <br />
> 20th International Conference on Integrated Formal Methods (iFM 2025)

The repository also includes scripts to reproduce the results reported in Table 1 and Table 2 of the paper and to check every refinement step in simulation mode.

Overview of Files
-----------------

The script `run-tlc.sh` runs the model checker TLC in model checking mode for the scenarios that are listed in Table 1 and Table 2 in the paper and in simulation mode for a model for each refinement step.

For each of the main specifications shown in Figure 4, there is a file containing the definition of the specification (see below "Specifications").

Additionally, there are specifications named in the form `SpecificationXtoY` that extend one of the main specifications with auxiliary variables to allow for defining a refinement mapping from specification X to specification Y.

The specifications use modules that define the concrete actions:
  - `PaymentChannelUser.tla` specifies the actions that a user performs for channel management (opening, updating, closing).
  - `HTLCUser.tla` specifies the actions that a user performs for making payments (sending invoices, adding HTLCs, fulfilling HTLCs, ...).
  - `PCAbstract.tla` specifies the actions of an idealized channel.
  - `LedgerTime.tla` specifies the advancement of time.
  - `MultiHopMock.tla` mocks for a channel c the actions that happen in other channels and have an effect on channel c.

The remaining .tla files contain helper functions.

The files in the \*.toolbox directories specify the scenarios to be model checked.

How to Run
----------

The recommended way is to run the model checker directly on your Unix system. This requires `java` to be in your `$PATH`.
Alternatively, you can use the docker image provided. Note that the model checker can be much slower when using docker compared to native execution.
The following explanation assumes that the working directory is the root directory of this repository.

### Natively

Download the model checker using the script `./download-tlc.sh`. This creates the file `tla2tools.jar` in the current directory.
Skip the next section about docker and continue with the section 'Model Checking'.

### Using Docker

Load the provided docker image: `docker load < docker-tlc-image.tar`
Alternatively, download the image from docker hub: `docker pull matthias25/tlc` If you downloaded the image from docker hub, use `matthias25/tlc` instead of `tlc` in the subsequent command.

Then, run the container with: ```docker run -v $(pwd):/work --rm -it tlc```
The option `-v` mounts the current directory in the docker container. The option `--rm` specifies that the docker container should be deleted after termination. The option `-it` starts an interactive shell inside the container.

### Model Checking

The model checker can be started with the script `./run-tlc.sh`.
The script takes two parameters. The first parameter is required and specifies which model checking jobs should be run; the second parameter points to the file `tla2tools.jar`. When using docker, the second parameter can be omitted.

For a smoke test, start the script using the parameter `--smoke-test`: `./run-tlc.sh --smoke-test tla2tools.jar`
The script creates a directory `output` where the output files are located and starts the model checker for a very simple model. After a couple of seconds, the script should terminate with the last line being `Successfully checked smoke_test.`.

To run the actual models that have been used for the paper, the following options are available for the first parameter of the script `./run-tlc.sh`.

| Value    |                         Models                   | Runtime (40 cores) |
|----------|--------------------------------------------------|--------------------|
| --brief  | C1, C2, C3,         M1                           | ~ 30 min           |
| --medium | C1, C2, C3,         M1, M2, M3                   | ~ 2 hours          |
| --long   | C1, C2, C3, C4,     M1, M2, M3, M4, M5, S1 - S9  | ~ 2 days           |
| --all    | C1, C2, C3, C4, C5, M1, M2, M3, M4, M5, S1 - S9  | ~ 7 weeks          |

In the third column, the expected runtime on a server with a CPU with 40 physical cores is given (native execution without docker).
Using only two cores, the runtime for the value `--brief` is about TODO TODO TODO.

In the second column, the identifiers C1 to C5 refer to the entries in Table 1 (as in the paper).
Analogously, we use the identifiers M1 to M5 for the entries in Table 2.
**Simulation**: The identifiers S1 to S9 refer to simulation runs.
While the model checker TLC explores the state space of the models C1 to C5 and M1 to M5 exhaustively, we use simulation to check models that are too large for an exhaustive exploration. In simulation mode, the model checker creates and checks random behaviors. In simulation mode, the model checker TLC terminates only if a violation has been found. Therefore, the script `./run-tlc.sh` stops each simulation run after one hour has passed.
The nine simulation models check the following refinement steps (roman numbers refer to specifications):

| Model | Refinement Step |
|-------|-----------------|
| S1    | (I) => (V)      |
| S2    | (I) => (II)     |
| S3    | (II) => (V)     |
| S4    | (II) => (III)   |
| S5    | (III) => (V)    |
| S6    | (III) => (IV)   |
| S7    | (IV) => (V)     |
| S7    | (IV) => (I)     |
| S8    | (IIa) => (IIIa) |
| S9    | (II) => (IIa)   |

**Results:**
Results of the model checking runs can be obtained from the logs created in the directory `output`.

With the command `tail -n 9 output/*.log` you can inspect the tail of all logs where the most important information is located.
The following listing shows an exemplary output enriched with three comments for explanation.

```
Model checking completed. No error has been found. # This line shows that the model checking run was successful.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 6.0E-8
  based on the actual fingerprints:  val = 7.0E-9
4612656 states generated, 252932 distinct states found, 0 states left on queue. # This line shows the number of all generated states (including duplicates) and the number of distinct states. The number of distinct states is the size of the state space.
The depth of the complete state graph search is 46.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 12 and the 95th percentile is 3).
Finished in 52min 35s at (2025-08-20 17:25:09) # This line shows the runtime.
```

The output of the simulation runs S1 to S9 should consist only of progress messages similar to the following example.
If a simulation run has failed, a trace that violates the checked property can be found at the tail of the output.

```
Progress: 692531 states checked, 66 traces generated (trace length: mean=22, var(x)=1005, sd=32)
```

Specifications
--------------

### Specification (I)

Specification (I), defined in `SpecificationI.tla` is our TLA+ specification of Lightning.
Each step is one of the following:
  - A user makes a step in a payment channel, or
  - a user makes a step for multi-hop payments, or
  - time advances, or
  - the system terminates if all channels have been closed.

### Specification (II)

Specification (II), defined in `SpecificationII.tla`, equals specification (I) except for how time advances. As explained in the paper in Section VI.A, time advances in specification (II) from one zone (group of bisimilar states) to the next zone instead of allowing for time to advance to every single point in time.

### Specification (IIa)

Specification (IIa), defined in `SpecificationIIa.tla`, models a single payment channel with two users that are part of specification (II). To model effects that other channels have on the payment channel, the state of the specification can also be changed by actions of the module defined in `MultiHopMock.tla`.

### Specification (III)

Specification (III), defined in `SpecificationIII.tla`, models idealized payment channels instead of modeling each payment channel by modeling two users exchanging messages and transactions.

### Specification (IIIa)

Specification (IIIa), defined in `SpecificationIIIa.tla`, models a single idealized payment channel. As in specification (IIa), the effects of other channels on the payment channel are mocked.

### Specification (IV)

Specification (IV), defined in `SpecificationIV.tla`, equals specification (III) except for how time advances. Specification (IV) uses the same approach for advancing time as specification (II).

### Specification (V)

Specification (V), defined in `SpecificationV.tla`, is the security property presented in the paper in Figures 3 to 5 (Figure 2 contains an excerpt).

Models for Model Checking
-------------------------

### Models for Refinement Mapping 2a

The following table lists the files for the models that we used to verify the refinement mapping 2a.
The IDs correspond to the IDs of the scenarios used in the paper in Table 1.

| ID |                         File                          |
|----|-------------------------------------------------------|
| C1 | SpecificationIIatoIIIa.toolbox/RefinementA3/MC.tla    |
| C2 | SpecificationIIatoIIIa.toolbox/RefinementA3ToC/MC.tla |
| C3 | SpecificationIIatoIIIa.toolbox/RefinementCToD/MC.tla  |
| C4 | SpecificationIIatoIIIa.toolbox/RefinementA5B3/MC.tla  |
| C5 | SpecificationIIatoIIIa.toolbox/RefinementA5A3/MC.tla  |

The models C1 to C5 are models for specification `SpecificationIIatoIIIa` which extends specification (IIa) by the refinement mapping from specification (IIa) to specification (IIIa).
The property checked by the models C1 to C5 is the property `SpecificationIIIa!SpecIIIa` where `SpecificationIIIa` is an instance of specification (IIIa) created by a refinement mapping from specification (IIa) and `SpecIIIa` is the formula for specification (IIIa).

### Models for Refinement Mapping 4

The following tables lists the files for the models that we used to verify the refinement mapping 4.

|                   Scenario                                                                               |                    File                    |
|----------------------------------------------------------------------------------------------------------|--------------------------------------------|
| Payment from user A over B to user C                                                                     | SpecificationIV.toolbox/MultiA3/MC.tla     |
| Two payments: Payment from user A over B to C and payment from user C over B to A                        | SpecificationIV.toolbox/MultiA3C2/MC.tla   |
| Two concurrent payments: Payment from user A over B to C and payment from user A to B                    | SpecificationIV.toolbox/MultiA3A2/MC.tla   |
| Three payments: Payment from user A over B to C, payment from user B to A, and payment from user B to C  | SpecificationIV.toolbox/MultiA3B1B1/MC.tla |
| Payment from user A over B, C and D to user E                                                            | SpecificationIV.toolbox/MultiAE3/MC.tla    |

### Models for Simulation

The following table lists the refinements and the files that contain a model to verify the refinement.
These models are too large for model checking but they can be verified by random state exploration using TLC's simulation mode.

| Refinement  |                         File                         |
|-------------|------------------------------------------------------|
| I -> V      | SpecificationI.toolbox/RefineSpecV/MC.tla            |
| I -> II     | SpecificationItoII.toolbox/RefineSpecII/MC.tla       |
| II -> V     | SpecificationII.toolbox/Model/MC.tla                 |
| II -> III   | SpecificationIItoIII.toolbox/RefineSpecIII/MC.tla    |
| III -> V    | SpecificationIII.toolbox/Model/MC.tla                |
| III -> IV   | SpecificationIIItoIV.toolbox/RefineSpecIV/MC.tla     |
| IV -> V     | SpecificationIV.toolbox/Model/MC.tla                 |
| IIa -> IIIa | SpecificationIIatoIIIa.toolbox/RefineSpecIIIa/MC.tla |
| II -> IIa   | SpecificationIItoIIa.toolbox/RefineSpecIIa/MC.tla    |



