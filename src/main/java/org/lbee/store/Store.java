package org.lbee.store;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.instrumentation.trace.VirtualField;

public class Store {

    private final Map<String, String> store;
    private final Map<Transaction, Map<String, String>> snapshots;
    private final List<Transaction> openTransactions;
    private long lastTransactionId = 0;

    private final Map<Transaction, Set<String>> written;
    private final Map<Transaction, Set<String>> missed;

    // Tracing
    private TLATracer tracer;
    private VirtualField traceTx;
    private VirtualField traceWritten;

    public Store() {
        this.store = new HashMap<>();
        this.snapshots = new HashMap<>();
        this.openTransactions = new ArrayList<>();
        this.written = new HashMap<>();
        this.missed = new HashMap<>();
    }

    public Store(TLATracer tracer) {
        this();
        this.tracer = tracer;
        this.traceTx = tracer.getVariableTracer("tx");
        this.traceWritten = tracer.getVariableTracer("written");
    }

    public synchronized Transaction open() throws IOException {
        // TODO: synchronize only on lastTransactionId
        Transaction transaction = new Transaction(this.lastTransactionId++);
        openTransactions.add(transaction);
        snapshots.put(transaction, new HashMap<>());
        written.put(transaction, new HashSet<>());
        missed.put(transaction, new HashSet<>());

        System.out.println("Open " + transaction);
        
        this.traceTx.add(transaction.getId()+"");
        this.traceWritten.getField(transaction.getId()+"").clear();
        this.tracer.log();

        return transaction;
    }

    public void add(Transaction transaction, String key, String value) throws KeyExistsException, IOException {
        System.out.println("Add (" + transaction + "): " + key + " " + value);

        final Map<String, String> snapshot = snapshots.get(transaction);
        // if key already exists throw exception
        if (snapshot.containsKey(key)) {
            throw new KeyExistsException();
        }
        // Change value in snapshot store
        snapshot.put(key, value);
        written.get(transaction).add(key);

        // trace
        this.traceWritten.getField(transaction.getId()+"").add(key);
        this.tracer.log();
    }

    public void update(Transaction transaction, String key, String value) throws KeyNotExistsException, ValueExistsException, IOException {
        System.out.println("Update (" + transaction + "): " + key + " " + value);

        final Map<String, String> snapshot = snapshots.get(transaction);
        // if key already exists throw exception
        if (!snapshot.containsKey(key)) {
            throw new KeyNotExistsException();
        }
        if (snapshot.get(key).equals(value)) {
            throw new ValueExistsException();
        }
        // Change value in snapshot store
        snapshot.put(key, value);
        written.get(transaction).add(key);
        
        // trace
        this.traceWritten.getField(transaction.getId()+"").add(key);
        this.tracer.log();
    }

    public void remove(Transaction transaction, String key) throws KeyNotExistsException, IOException {
        System.out.println("Remove (" + transaction + "): " + key);

        final Map<String, String> snapshot = snapshots.get(transaction);
        // if key doesn't exist throw exception
        if (!snapshot.containsKey(key)) {
            throw new KeyNotExistsException();
        }
        snapshot.remove(key);
        written.get(transaction).add(key);

        // trace
        this.traceWritten.getField(transaction.getId()+"").add(key);
        this.tracer.log();
    }

    public String read(String key) {
        System.out.println("Read " + key);

        return store.get(key);
    }

    public synchronized boolean close(Transaction transaction) throws IOException {
        // compute the intersection between written and missed
        // Set<String> intersection = new HashSet<>(written.get(transaction));
        Set<String> intersection = written.get(transaction);
        intersection.retainAll(missed.get(transaction));
        // System.out.println("Close: ("+transaction+"): written: "+written.get(transaction)+", missed: "+missed.get(transaction)+", intersection: "+intersection);
        // check if the the intersection of written and missed is empty; rollback if not
        if(!intersection.isEmpty()) {
            // remove the transaction from the pool, snapshots, written and missed
            openTransactions.remove(transaction);
            snapshots.remove(transaction);
            written.remove(transaction);
            missed.remove(transaction);
            System.out.println("Rollback (" + transaction + "): " + intersection);
            return false;
        }
        // add the operation from snapshot to store
        final Map<String, String> snapshot = snapshots.get(transaction);
        for (String key : snapshot.keySet()) {
            store.put(key, snapshot.get(key));
        }
        // Add written log as missed for other open transactions
        for (Transaction tx : openTransactions) {
            missed.get(tx).addAll(written.get(transaction));
        }
        // remove the transaction from the pool, snapshots, written and missed
        openTransactions.remove(transaction);
        snapshots.remove(transaction);
        written.remove(transaction);
        missed.remove(transaction);
        System.out.println("Commit (" + transaction + "): " + snapshot);

        // trace
        this.traceTx.remove(transaction.getId()+"");
        this.traceWritten.getField(transaction.getId()+"").clear();
        this.tracer.log();
        return true;
    }

    public String toString() {
        return store.toString()+" - "+openTransactions.toString();
    }
}
