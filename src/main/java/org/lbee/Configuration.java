package org.lbee;

import java.util.List;

public class Configuration {

    public long nbTransactionLimit;
    public List<String> keys;

    public List<String> vals;

    public Configuration(List<String> keys, List<String> vals, long nbTransactionLimit) {
        this.keys = keys;
        this.vals = vals;
        this.nbTransactionLimit = nbTransactionLimit;
    }

}
