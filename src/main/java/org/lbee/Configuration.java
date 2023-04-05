package org.lbee;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Configuration {

    public final long nbTransactionLimit;
    public final List<String> keys;
    public final List<String> vals;
    private final List<String> txIds;

    public Configuration(List<String> keys, List<String> vals, long nbTransactionLimit) {
        this.keys = keys;
        this.vals = vals;
        this.nbTransactionLimit = nbTransactionLimit;

        this.txIds = new ArrayList<>();
        for (int i = 0; i < this.nbTransactionLimit; i++) {
            this.txIds.add("t" + (i + 1));
        }
    }

    public Map<String, Object> toHashMap() {
        return Map.of("Key", this.keys, "Val", this.vals, "TxId", this.txIds);
    }

}
