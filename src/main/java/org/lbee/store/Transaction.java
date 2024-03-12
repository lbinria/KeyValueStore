package org.lbee.store;

public class Transaction {
    // transaction guid
    private final long guid;
    // constructor
    public Transaction(long guid) {
        this.guid = guid;
    }
    // getter
    public long getGuid() {
        return guid;
    }
    // print transaction
    @Override
    public String toString() {
        return "T_" + guid;
    }
}
