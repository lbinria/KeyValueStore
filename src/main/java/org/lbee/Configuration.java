package org.lbee;

import java.util.*;

public class Configuration {

    public final long nbTransactionLimit;
    public final List<String> keys;
    public final List<String> vals;
    private final List<String> txIds;

    public Configuration(int nKeys, int nVals, int nbTransactionLimit, boolean randomGenerated) {
        this.keys = new ArrayList<>();
        this.vals = new ArrayList<>();
        this.txIds = new ArrayList<>();
        this.nbTransactionLimit = nbTransactionLimit;

        for (int i = 0; i < nKeys; i++) {
            this.keys.add(getLabel(randomGenerated, "k_", i + 1));
        }
        for (int i = 0; i < nVals; i++) {
            this.vals.add(getLabel(randomGenerated, "v_", i + 1));
        }
        for (int i = 0; i < nbTransactionLimit; i++) {
            this.txIds.add(getLabel(randomGenerated, "t_", i + 1));
        }
    }

    private String getLabel(boolean randomGenerated, String prefix, int i) {
        return randomGenerated ? prefix + UUID.randomUUID() : prefix + i;
    }

    public List<String> getKeys() { return keys; }
    public List<String> getVals() { return vals; }
    public List<String> getTxIds() { return txIds; }

    public Map<String, Object> toHashMap() {
        return Map.of("Key", this.keys, "Val", this.vals, "TxId", this.txIds);
    }

}
