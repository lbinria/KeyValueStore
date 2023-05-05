package org.lbee;

import org.lbee.instrumentation.clock.SharedClock;

import java.io.IOException;

public class Helpers {

    private static SharedClock clock;

    public static SharedClock getClock() throws IOException {
        if (clock == null)
            clock = new SharedClock("kvs.clock");

        return clock;
    }

}
