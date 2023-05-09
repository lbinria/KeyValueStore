package org.lbee;

import java.util.Random;

public class Helpers {

    // Random generator
    private final static Random random = new Random();

    /**
     * Pick up a random key from keys found in config
     * @param configuration Configuration from which pick up
     * @return A key
     */
    public static String pickRandomKey(Configuration configuration) {
        return configuration.getKeys().get(random.nextInt(configuration.getKeys().size()));
    }

    /**
     * Pick up a random val from vals found in config
     * @param configuration Configuration from which pick up
     * @return A value
     */
    public static String pickRandomVal(Configuration configuration) {
        return configuration.getVals().get(random.nextInt(configuration.getVals().size()));
    }

    /**
     * Pick up a random transaction id from transaction ids found in config
     * @param configuration Configuration from which pick up
     * @return A transaction id
     */
    public static String pickRandomTxId(Configuration configuration) {
        return configuration.getTxIds().get(random.nextInt(configuration.getTxIds().size()));
    }

}
