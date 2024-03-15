--------------------------- MODULE KeyValueStoreTrace ---------------------------

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, KeyValueStore, TVOperators, TraceSpec

KVS == INSTANCE KeyValueStore

(* Override CONSTANTS *)

(* Replace Nil constant *)
TraceNil == "null"

TraceKey ==
    ToSet(Config[1].Key)

TraceVal ==
    ToSet(Config[1].Val)

TraceTxId ==
    ToSet(Config[1].TxId)

(* Can be extracted from init *)
DefaultImplementation(varName) ==
    CASE varName = "store" -> [k \in Key |-> NoVal]
    []  varName = "tx" -> {}
    []  varName = "snapshotStore" -> [t \in TxId |-> [k \in Key |-> NoVal]]
    []  varName = "written" -> [t \in TxId |-> {}]
    []  varName = "missed" -> [t \in TxId |-> {}]

UpdateVariablesImplementation(t) ==
    /\
        IF "store" \in DOMAIN t
        THEN store' = UpdateVariable(store, "store", t)
        ELSE TRUE
    /\
        IF "tx" \in DOMAIN t
        THEN tx' = UpdateVariable(tx, "tx", t)
        ELSE TRUE
    /\
        IF "snapshotStore" \in DOMAIN t
        THEN snapshotStore' = UpdateVariable(snapshotStore, "snapshotStore", t)
        ELSE TRUE
    /\
        IF "written" \in DOMAIN t
        THEN written' = UpdateVariable(written, "written", t)
        ELSE TRUE
    /\
        IF "missed" \in DOMAIN t
        THEN missed' = UpdateVariable(missed, "missed", t)
        ELSE TRUE

(* Predicate actions *)
IsOpenTx ==
    /\ IsEvent("OpenTx")
    /\
        IF "event_args" \in DOMAIN logline THEN
            OpenTx(logline.event_args[1])
        ELSE
            \E t \in TxId : OpenTx(t)

IsRollbackTx ==
    /\ IsEvent("RollbackTx")
    /\
        IF "event_args" \in DOMAIN logline THEN
            RollbackTx(logline.event_args[1])
        ELSE
            \E t \in TxId : RollbackTx(t)

IsCloseTx ==
    /\ IsEvent("CloseTx")
    /\
        IF "event_args" \in DOMAIN logline THEN
            CloseTx(logline.event_args[1])
        ELSE
            \E t \in TxId : CloseTx(t)

IsAdd ==
    /\ IsEvent("Add")
    /\
        IF "event_args" \in DOMAIN logline THEN
            KVS!Add(logline.event_args[1], logline.event_args[2], logline.event_args[3])
        ELSE
            \E t \in TxId, k \in Key, v \in Val : KVS!Add(t, k, v)

IsUpdate ==
    /\ IsEvent("Update")
    /\
        IF "event_args" \in DOMAIN logline THEN
            Update(logline.event_args[1], logline.event_args[2], logline.event_args[3])
        ELSE
            \E t \in TxId, k \in Key, v \in Val : Update(t, k, v)

IsRemove ==
    /\ IsEvent("Remove")
    /\
        IF "event_args" \in DOMAIN logline THEN
            KVS!Remove(logline.event_args[1], logline.event_args[2])
        ELSE
            \E t \in TxId, k \in Key : KVS!Remove(t, k)

TraceNextImplementation ==
    \/ IsOpenTx
    \/ IsRollbackTx
    \/ IsCloseTx
    \/ IsAdd
    \/ IsUpdate
    \/ IsRemove

ComposedNext == FALSE

BaseSpec == Init /\ [][Next \/ ComposedNext]_vars

TraceAlias ==
    [
        \* TODO: Funny TLCGet("level")-1 could be removed if the spec has an
        \* TODO: auxiliary counter variable  i  .  Would also take care of
        \* TODO: the bug that TLCGet("level")-1 is not defined for the initial
        \* TODO: state.
        len |-> Len(Trace),
        log     |-> <<TLCGet("level"), Trace[TLCGet("level")]>>,
        snapshotStore |-> snapshotStore,
        written |-> written,
        enabled |-> [
            OpenTx |-> ENABLED \E t \in TxId : OpenTx(t) /\ UpdateVariables(Trace[TLCGet("level")]),
            RollbackTx |-> ENABLED \E t \in TxId : RollbackTx(t)  /\ UpdateVariables(Trace[TLCGet("level")]),
            CloseTx |-> ENABLED \E t \in TxId : CloseTx(t)  /\ UpdateVariables(Trace[TLCGet("level")]),
            Add |-> ENABLED \E t \in TxId, k \in Key, v \in Val : KVS!Add(t,k,v)  /\ UpdateVariables(Trace[TLCGet("level")]),
            Update |-> ENABLED \E t \in TxId, k \in Key, v \in Val : Update(t,k,v)  /\ UpdateVariables(Trace[TLCGet("level")]),
            Map |-> ENABLED UpdateVariables(Trace[TLCGet("level")])
        ]
    ]
-----------------------------------------------------------------------------

=============================================================================