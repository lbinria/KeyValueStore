package org.lbee.store;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Store {

    private final Map<String, String> store;
    private final Map<Transaction, Map<String, String>> snapshots;
    private final List<Transaction> openTransactions;
    private long lastTransactionId = 0;

    private final Map<Transaction, Set<String>> written;
    private final Map<Transaction, Set<String>> missed;

    public Store() {
        this.store = new HashMap<>();
        this.snapshots = new HashMap<>();
        this.openTransactions = new ArrayList<>();
        this.written = new HashMap<>();
        this.missed = new HashMap<>();
    }

    public synchronized Transaction open() {
        // TODO: synchronize only on lastTransactionId
        Transaction transaction = new Transaction(this.lastTransactionId++);
        openTransactions.add(transaction);
        snapshots.put(transaction, new HashMap<>());
        written.put(transaction, new HashSet<>());
        missed.put(transaction, new HashSet<>());

        System.out.println("Open " + transaction);
        
        return transaction;
    }

    public void add(Transaction transaction, String key, String value) throws KeyExistsException {
        System.out.println("Add (" + transaction + "): " + key + " " + value);

        final Map<String, String> snapshot = snapshots.get(transaction);
        // if key already exists throw exception
        if (snapshot.containsKey(key)) {
            throw new KeyExistsException();
        }
        // Change value in snapshot store
        snapshot.put(key, value);
        written.get(transaction).add(key);
        // TODO: Log modifications
    }

    public void update(Transaction transaction, String key, String value) throws KeyNotExistsException, ValueExistsException {
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
        // TODO: Log modifications
    }

    public void remove(Transaction transaction, String key) throws KeyNotExistsException {
        System.out.println("Remove (" + transaction + "): " + key);

        final Map<String, String> snapshot = snapshots.get(transaction);
        // if key doesn't exist throw exception
        if (!snapshot.containsKey(key)) {
            throw new KeyNotExistsException();
        }
        snapshot.remove(key);
        written.get(transaction).add(key);
        // TODO: Log modifications
    }

    public String read(String key) {
        System.out.println("Read " + key);

        return store.get(key);
    }

    public synchronized boolean close(Transaction transaction) {
        // compute the intersection between written and missed
        final Set<String> intersection = new HashSet<>(written.get(transaction));
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
        return true;
    }

    // get the set of keys in the store
    public Set<String> getKeys() {
        return store.keySet();
    }

    public String toString() {
        return store.toString()+" - "+openTransactions.toString();
    }
}
