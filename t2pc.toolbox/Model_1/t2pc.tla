----------------------------- MODULE t2pc ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT RM,       \* The set of participating resource managers, RM = 1..3
         RMMAYFAIL,
         TMMAYFAIL,
         ENABLEBTM \* Flag to enable the backup TM configuration
         
(***************************************************************************
A modified version of P2TCommit at http://lamport.azurewebsites.net/tla/two-phase.html
Transaction manager (TM) is added.

 `.
--algorithm TransactionCommit {
  variable rmState = [rm \in RM |-> "working"] ;
                      
           \* The state of the transation manager
           tmState = "init";    
           \* Initial state of the backup TM set to inactive
           btmState = "inactive";

  define {
    \* can commit when only all RM are either in prepared state or have committed and the TM state is not in abort state
    canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed", "failed"} /\ btmState # "abort" /\ tmState # "abort"
    \* can abort when only all RM are not in committed state and the TM state is not committed
    canAbort == (\A rm \in RM : rmState[rm] # "committed" /\ (tmState # "commit" /\ btmState # "commit"))
   }
   
  macro Prepare(p) {
      \* ignore if already in prepared state
      if(rmState[p] # "prepared"){
         await rmState[p] = "working";
         rmState[p] := "prepared" ;
      }      
   }

    
  macro Fail(p) {
    \* If RMMAYFAIL is True then the state of the RM may become failed
    if( RMMAYFAIL ) {
         either {
                 rmState[p] := "failed"
                }
         or skip;
     }; 
  }
  
  macro Decide(p) {
   \* each RM can access its own state and the TM state or Backup TM state
   \* Each RM will consult the Backup TM only when the tmState is hidden and Backup TM is enabled
    either { when /\ rmState[p] = "prepared" 
                  /\ (tmState="commit" \/ (tmState = "hidden" /\ ENABLEBTM /\ btmState = "commit"));
             rmState[p] := "committed"
           }
           \* RM can abort if its in working or prepared state provided TM sends abort
    or     { when /\ rmState[p] \in {"working", "prepared"}
                  /\ (tmState="abort" \/ (tmState = "hidden" /\ ENABLEBTM /\ btmState = "abort"));
             rmState[p] := "aborted"
           }
           \* RM can spontaneously decide to abort if its in working state 
    or    { when /\ rmState[p] \in {"working"};
             rmState[p] := "aborted"
          }  
   }
   
  fair process (RManager \in RM) {
    \* an RM can do any of the following when in working and prepared state
    RS: while (rmState[self] \in {"working", "prepared"}) { 
      either Prepare(self) or Decide(self) or Fail(self)}  
      
   }
   
  \* Process for Transaction Manager 
  fair process (TManager=0) {
   \* TMANAGER is operational process only as long as the tmState is not hidden  
   TS:  if(tmState # "hidden") {
            either { await canCommit;
                      TC: tmState := "commit";
                      F1: if( TMMAYFAIL) {
                             \* record the active tmState in backup TM
                             btmState := tmState;
                             tmState := "hidden";
                             
                           } \* if
                     }\* either
                  or { 
                       await canAbort;
                       TA: tmState := "abort";
                       F2: if( TMMAYFAIL) {
                              \* record the active tmState in backup TM
                              btmState := tmState;
                              tmState := "hidden";
                         } \* if                  
                     }\* or
     } \* if     
  }
  
  \* Process for the Backup Transaction Manager
  fair process (BTManager=10) {
    \* Backup TM becomes active only when TM state is hidden and ENABLEBTM flag is set
    \* to true     
    BTS: if(ENABLEBTM /\ tmState = "hidden") {
           either { 
                     await canCommit;
                     BTC: btmState := "commit";
                 }\* either
                 or { 
                       await canAbort;
                       BTA: btmState := "abort";
                     }\* or
       }\* if
  }
}
 .'
 
Below is the algorithm's translation.  The translation defines
Termination to be the temporal formula asserting that eventually
all processes terminate.
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES rmState, tmState, btmState, pc

(* define statement *)
canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed", "failed"} /\ btmState # "abort" /\ tmState # "abort"

canAbort == (\A rm \in RM : rmState[rm] # "committed" /\ (tmState # "commit" /\ btmState # "commit"))


vars == << rmState, tmState, btmState, pc >>

ProcSet == (RM) \cup {0} \cup {10}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ btmState = "inactive"
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TS"
                                        [] self = 10 -> "BTS"]

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared"}
                  THEN /\ \/ /\ IF rmState[self] # "prepared"
                                   THEN /\ rmState[self] = "working"
                                        /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED rmState
                          \/ /\ \/ /\ /\ rmState[self] = "prepared"
                                      /\ (tmState="commit" \/ (tmState = "hidden" /\ ENABLEBTM /\ btmState = "commit"))
                                   /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                \/ /\ /\ rmState[self] \in {"working", "prepared"}
                                      /\ (tmState="abort" \/ (tmState = "hidden" /\ ENABLEBTM /\ btmState = "abort"))
                                   /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                                \/ /\ /\ rmState[self] \in {"working"}
                                   /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                          \/ /\ IF RMMAYFAIL
                                   THEN /\ \/ /\ rmState' = [rmState EXCEPT ![self] = "failed"]
                                           \/ /\ TRUE
                                              /\ UNCHANGED rmState
                                   ELSE /\ TRUE
                                        /\ UNCHANGED rmState
                       /\ pc' = [pc EXCEPT ![self] = "RS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmState
            /\ UNCHANGED << tmState, btmState >>

RManager(self) == RS(self)

TS == /\ pc[0] = "TS"
      /\ IF tmState # "hidden"
            THEN /\ \/ /\ canCommit
                       /\ pc' = [pc EXCEPT ![0] = "TC"]
                    \/ /\ canAbort
                       /\ pc' = [pc EXCEPT ![0] = "TA"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << rmState, tmState, btmState >>

TC == /\ pc[0] = "TC"
      /\ tmState' = "commit"
      /\ pc' = [pc EXCEPT ![0] = "F1"]
      /\ UNCHANGED << rmState, btmState >>

F1 == /\ pc[0] = "F1"
      /\ IF TMMAYFAIL
            THEN /\ btmState' = tmState
                 /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED << tmState, btmState >>
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TA == /\ pc[0] = "TA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![0] = "F2"]
      /\ UNCHANGED << rmState, btmState >>

F2 == /\ pc[0] = "F2"
      /\ IF TMMAYFAIL
            THEN /\ btmState' = tmState
                 /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED << tmState, btmState >>
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TManager == TS \/ TC \/ F1 \/ TA \/ F2

BTS == /\ pc[10] = "BTS"
       /\ IF ENABLEBTM /\ tmState = "hidden"
             THEN /\ \/ /\ canCommit
                        /\ pc' = [pc EXCEPT ![10] = "BTC"]
                     \/ /\ canAbort
                        /\ pc' = [pc EXCEPT ![10] = "BTA"]
             ELSE /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED << rmState, tmState, btmState >>

BTC == /\ pc[10] = "BTC"
       /\ btmState' = "commit"
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED << rmState, tmState >>

BTA == /\ pc[10] = "BTA"
       /\ btmState' = "abort"
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED << rmState, tmState >>

BTManager == BTS \/ BTC \/ BTA

Next == TManager \/ BTManager
           \/ (\E self \in RM: RManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)
        /\ WF_vars(BTManager)

\* For termination, all RM which have not failed should be in either 'aborted' or
\* 'committed' state, TM or BTM state should be matching the RM states
\* all process's program counter should be at 'Done'
Termination == <>((
                  (\A rm \in RM: rmState[rm] # "failed" => rmState[rm] = "committed" /\ (tmState="commit" \/ (tmState="hidden" /\ btmState="commit"))) 
               \/ (\A rm \in RM: rmState[rm] # "failed" => rmState[rm] = "aborted" /\ (tmState="abort" \/ (tmState="hidden" /\ btmState="abort"))))
               /\ (\A self \in ProcSet: pc[self] = "Done"))
\* END TRANSLATION

(***************************************************************************)
(* The invariants:                                                         *)
(***************************************************************************)
TypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted", "failed"}]
  /\ tmState \in {"init", "hidden", "commit", "abort"}
  /\ btmState \in {"inactive", "commit", "abort"}
  

Consistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

                         
THEOREM Spec => [](TypeOK /\ Consistent)

=============================================================================
\* Modification History
\* Last modified Tue Dec 05 19:16:48 EST 2017 by varunjai
\* Last modified Tue Oct 11 08:14:15 PDT 2011 by lamport
\* Created Mon Oct 10 05:31:02 PDT 2011 by lamport
Members:
-------- 
Name: Sneha Mehta
UBIT Name: snehameh
Person# - 50245877

Name: Varun Jain
UBIT Name: varunjai 
Person# - 50247176


Explaination
--------------
This program emulates 2 phase commit under the problem conditions

TypeOK Property:
The states for all resource manager,  transaction manager and backup transaction manager
are defined.

Termination Property:
 - All the Resource managers which are not failed are either in the committed state or the
   aborted state 
 - The transaction manager state is also set accordingly to commit or abort state accordingly
 - In case the transaction manager is 'hidden' then backup transaction manager state should be
   set to commit or abort accordingly.

Consistency Property
- No two Resource managers can be in conflicting states like - aborted and committed.


1.1 RMMAYFAIL = FALSE and TMMAYFAIL = FALSE
    
    No errors were observed as no failures occurred and the 2 phase commit protocol was
    neatly executed satisfying CONSISTENCY and Termination properties.
      
    RMMAYFAIL = TRUE and TMMAYFAIL = FALSE
    
    No errors were observed as though some resource manager failures occurred, the 2 phase 
    commit protocol was neatly executed satisfying CONSISTENCY and Termination properties.   


1.2 RMMAYFAIL = FALSE and TMMAYFAIL = TRUE, no backup TM
    Model: 4 RM nodes, 1 TM
    
    Observations:    
    1. Model fails with temporal property or termination property violation in this case.  
       
       /\  pc = (0 :> "Done" @@ 1 :> "RS" @@ 2 :> "Done" @@ 3 :> "Done" @@ 4 :> "Done")
       /\  rmState = <<"prepared", "aborted", "aborted", "aborted">>
       /\  tmState = "hidden"
       
    2. The model failed because once the TM failed during the run, Resource managers which
       decided to go to 'prepared' state could no longer terminate as they were unable
       to access TM state and hence could not move to states 'committed' or 'aborted'.
       
       
1.3 When both RMMAYFAIL=TRUE and TMMAYFAIL=TRUE, and ENABLEBTM=TRUE (the Backup TM is enabled)
    Model: 4 RM nodes, 1 TM, 1 BTM (backup TM)  
    
    Observations:
    1. Model passes without any failures. The program satisfies both TERMINATION and CONSISTENCY. 
       This is because on failure of the TM, the BTM becomes active and it is assumed that the BTM does not fail.
       The resource managers are now being serviced by the BTM similar to the TM.
       
       
          
       
