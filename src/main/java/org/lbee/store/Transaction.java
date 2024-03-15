package org.lbee.store;

public class Transaction {
    // transaction guid
    private final long id;
    // constructor
    public Transaction(long guid) {
        this.id = guid;
    }
    // getter
    public long getId() {
        return id;
    }
    // print transaction
    @Override
    public String toString() {
        return "T_" + id;
    }
}
