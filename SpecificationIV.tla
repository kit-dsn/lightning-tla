-------------------------- MODULE SpecificationIV --------------------------

(***************************************************************************)
(* Time-optimized specification of Lightning with idealized channels.      *)
(***************************************************************************)

EXTENDS SpecificationIII

(***************************************************************************)
(* Points in time to which time should advance with the time-optimization. *)
(* Proof of correctness in the appendix of the extended version of the     *)
(* paper.                                                                  *)
(***************************************************************************)
SpecIVNCTPs == UNION {AbstractChannel!TimelockRegions(c, UsersOfChannel[c][1], UsersOfChannel[c][2]) : c \in ActiveChannels}
                                \cup UNION UNION { { HU!TimelockRegions(c, u, CHOOSE o \in UsersOfChannelSet(c) : o # u) : u \in UsersOfChannelSet(c)}
                                                    : c \in ActiveChannels}

relETP == SpecIVNCTPs \cup {t + 1 : t \in TimeBounds}

LedgerTimeInstanceIV == INSTANCE LedgerTime WITH
    Time <- LedgerTime,
    TimeBounds <- TimeBounds,
    NextChangingTimePoints <- relETP

AdvanceLedgerTimeIV ==
    /\  \/  /\ LedgerTimeInstanceIV!Next
            /\ UNCHANGED <<UserHonest>>
    /\ UNCHANGED varsWithoutLedgerTime

NextIV ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeIV
    \/ \E c \in ActiveChannels : AbstractChannel!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!Next(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosed
    
NextIVFair ==
  /\ LedgerTime < 100
  /\
    \/ AdvanceLedgerTimeIV
    \/ \E c \in ActiveChannels : AbstractChannel!Next(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][1], UsersOfChannel[c][2])
    \/ \E c \in ActiveChannels : HU!NextFair(c, UsersOfChannel[c][2], UsersOfChannel[c][1])
    \/ WithdrawBalancesAfterChannelClosed
    

SpecIV ==
    /\ Init
    /\ [][NextIV]_vars
    /\ WF_vars(NextIVFair)

=============================================================================
