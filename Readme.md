TLA+ Source Files for Paper "Model Checking the Security of the Lightning Network"
===========================================================================================================

Overview of files
-----------------

The script `download-and-run-tlc.sh` downloads the model checker TLC and runs TLC in model checking mode for the scenarios that are listed in Table I and Table II in the paper and in simulation mode for a model for each refinement step.

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

Specification (V), defined in `SpecificationV.tla`, is the security property presented in the paper in Figure 1.

Models for Model Checking
-------------------------

The following table lists the files for the models that we used to verify the refinement mapping 2a.
The IDs correspond to the IDs of the scenarios used in the paper in Table 1.

| ID |                         File                          |
|----|-------------------------------------------------------|
| C1 | SpecificationIIatoIIIa.toolbox/RefinementA3/MC.tla    |
| C2 | SpecificationIIatoIIIa.toolbox/RefinementA3ToC/MC.tla |
| C3 | SpecificationIIatoIIIa.toolbox/RefinementCToD/MC.tla  |
| C4 | SpecificationIIatoIIIa.toolbox/RefinementA5B3/MC.tla  |
| C5 | SpecificationIIatoIIIa.toolbox/RefinementA5A3/MC.tla  |

The following tables lists the files for the models that we used to verify the refinement mapping 4.

|                   Scenario                                                                               |                    File                    |
|----------------------------------------------------------------------------------------------------------|--------------------------------------------|
| Payment from user A over B to user C                                                                     | SpecificationIV.toolbox/MultiA3/MC.tla     |
| Two payments: Payment from user A over B to C and payment from user C over B to A                        | SpecificationIV.toolbox/MultiA3C2/MC.tla   |
| Two concurrent payments: Payment from user A over B to C and payment from user A to B                    | SpecificationIV.toolbox/MultiA3A2/MC.tla   |
| Three payments: Payment from user A over B to C, payment from user B to A, and payment from user B to C  | SpecificationIV.toolbox/MultiA3B1B1/MC.tla |
| Payment from user A over B, C and D to user E                                                            | SpecificationIV.toolbox/MultiAE3/MC.tla    |

Models for Simulation
---------------------

The following table lists the refinements and the files that contain a model to verify the refinement.
These models are too large for model checking but they can be verified by random state exploration using TLC's simulation mode (see `download-and-run-tlc.sh`).

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



