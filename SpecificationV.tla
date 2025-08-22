--------------------------- MODULE SpecificationV ---------------------------

(***************************************************************************)
(* Specification of the main security property                             *)
(***************************************************************************)

(***************************************************************************)
(* Variables for the external balance on the blockchain, internal balance, *)
(* set of payments, and whether a user is honest.  Each variable is a      *)
(* function that contains a variable for each id in UserIds.               *)
(***************************************************************************)
VARIABLES BlockchainBalances, ChannelBalances,
    Payments, Honest
CONSTANTS UserIds, InitialPayments, Numbers

(***************************************************************************)
(* Specification of an ideal user.                                         *)
(***************************************************************************)
IdealUser(user) == INSTANCE IdealUser WITH
    UserId <- user,
    ChannelBalance <- ChannelBalances[user],
    BlockchainBalance <- BlockchainBalances[user],
    Payments <- Payments[user],
    Honest <- Honest[user]
    
(***************************************************************************)
(* Specification of correct payments between users.                        *)
(***************************************************************************)
IdealPayments == INSTANCE IdealPayments
    
Spec ==
    /\ \A user \in UserIds : IdealUser(user)!Spec
    /\ IdealPayments!Spec

=============================================================================
