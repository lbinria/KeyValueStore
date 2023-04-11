package org.lbee;

import org.lbee.instrumentation.NDJsonTraceProducer;
import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.TraceProducerException;

public class TraceSingleton {

    private static TraceInstrumentation instance;

    public static TraceInstrumentation getInstance() {
        if (instance==null)
            instance = new TraceInstrumentation(new NDJsonTraceProducer("kvs.ndjson"), false);

        return instance;
    }

    public static boolean tryCommit() {
        try {
            getInstance().commitChanges();
            return true;
        } catch (TraceProducerException e) {
            System.out.println(e.toString());
            e.printStackTrace();
            return false;
        }
    }

}
