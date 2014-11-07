/*
 * Copyright (c) 1999-2014, Ecole des Mines de Nantes
 * All rights reserved.
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the Ecole des Mines de Nantes nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE REGENTS AND CONTRIBUTORS BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package solver;


import util.logger.ILogger;
import util.logger.LoggerFactory;

import java.util.Properties;

/**
 * Global settings
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 01/08/12
 */
public enum Configuration {
    ;

    private static final ILogger logger = LoggerFactory.getLogger();

    private static final String UDPATH = "/user.properties";

    private static final String PATH = "/configuration.properties";

    private static Properties properties = new Properties();

    static {
        try {
            properties.load(Configuration.class.getResourceAsStream(PATH));
        } catch (Exception e) {
            logger.errorf("Unable to load %s file from classpath.\n%s\n", PATH, e);
            System.exit(1);
        }
        // then override values, if any
        try {
            properties.load(Configuration.class.getResourceAsStream(UDPATH));
        } catch (NullPointerException e) {
            //            logger.warn("No user defined properties. Skip loading " + UDPATH + " file.");
        } catch (Exception e) {
            logger.errorf("Unable to load %s file from classpath.\n%s\n", UDPATH, e);
        }
        {
            String values = properties.getProperty("FINE_EVENT_QUEUES");
            values = values.substring(1, values.length() - 1);
            String[] values_ = values.split(",");
            short[] shorts = new short[values_.length];
            for (int i = 0; i < values_.length; i++) {
                shorts[i] = Short.parseShort(values_[i]);
            }
            FINE_EVENT_QUEUES = shorts;
        }
        {
            String values = properties.getProperty("COARSE_EVENT_QUEUES");
            values = values.substring(1, values.length() - 1);
            String[] values_ = values.split(",");
            short[] shorts = new short[values_.length];
            for (int i = 0; i < values_.length; i++) {
                shorts[i] = Short.parseShort(values_[i]);
            }
            COARSE_EVENT_QUEUES = shorts;
        }
    }

    public static final String WELCOME_TITLE = properties.getProperty("WELCOME_TITLE");

    public static final String CALLER = properties.getProperty("CALLER");

    // Set to true to plug explanation engine in -- enable total disconnection
    public static final boolean PLUG_EXPLANATION = Boolean.parseBoolean(properties.getProperty("PLUG_EXPLANATION"));

    // Set to true to print explanation information
    public static final boolean PRINT_EXPLANATION = Boolean.parseBoolean(properties.getProperty("PRINT_EXPLANATION"));

    // Set to true to add propagators to explanation
    public static final boolean PROP_IN_EXP = Boolean.parseBoolean(properties.getProperty("PROP_IN_EXP"));

    // Set to true to print propagation information
    public static final boolean PRINT_PROPAGATION = Boolean.parseBoolean(properties.getProperty("PRINT_PROPAGATION"));

    // Set to true to print event occurring on variables
    public static final boolean PRINT_VAR_EVENT = Boolean.parseBoolean(properties.getProperty("PRINT_VAR_EVENT"));

    // Set to true to print scheduling information
    public static final boolean PRINT_SCHEDULE = Boolean.parseBoolean(properties.getProperty("PRINT_SCHEDULE"));

    // Set to true to allow the creation of views in the VariableFactory.
    // Creates new variables with channeling constraints otherwise.
    public static final boolean ENABLE_VIEWS = Boolean.parseBoolean(properties.getProperty("ENABLE_VIEWS"));

    public enum Idem {
        disabled, // does not anything
        error, // print an error message when a propagator is not guaranteed to be idempotent -- fir debug only
        force // extra call to Propagator.propagate(FULL_PROPAGATION) when no more event is available
    }

    // Define how to react when a propagator is not ensured to be idempotent
    // disabled : does not anything
    // error: print an error message when a propagator is not guaranteed to be idempotent -- fir debug only
    // force : extra call to Propagator.propagate(FULL_PROPAGATION) when no more event is available
    public static final Idem IDEMPOTENCY = Idem.valueOf(properties.getProperty("IDEMPOTENCY"));

    // Defines the rounding precision for multicostregular algorithm
    // MUST BE < 13 as java messes up the precisions starting from 10E-12 (34.0*0.05 == 1.70000000000005)
    public static final int MCR_PRECISION = Integer.parseInt(properties.getProperty("MCR_PRECISION"));

    // Defines the smallest used double for multicostregular
    public static final double MCR_DECIMAL_PREC = Math.pow(10.0, -MCR_PRECISION);

    // Defines, for each priority, the queue the propagators of this priority should be scheduled in
    // /!\ for advanced use only
    // 1. For fine events
    public static final short[] FINE_EVENT_QUEUES;
    // 2. For coarse events
    public static final short[] COARSE_EVENT_QUEUES;

    // Define the maximum domain size to force integer variable to be enumerated
    // instead of bounded while calling VariableFactory.integer
    public static final int MAX_DOM_SIZE_FOR_ENUM = Integer.parseInt(properties.getProperty("MAX_DOM_SIZE_FOR_ENUM"));

    // Set to true to allow intension constraint to extension constraint substitution
    public static final boolean ENABLE_TABLE_SUBS = Boolean.parseBoolean(properties.getProperty("ENABLE_TABLE_SUBS"));

    // Define the maximum domain size to enable intension constraint to extension constraint substitution
    // Only checked when ENABLE_TABLE_SUBS is set to true
    public static final int MAX_TUPLES_FOR_TABLE_SUBS = Integer.parseInt(properties.getProperty("MAX_TUPLES_FOR_TABLE_SUBS"));

    // Define the search binder path
    public static final String SEARCH_BINDER_PATH = properties.getProperty("SEARCH_BINDER_PATH");

    // MDD compacting only once at the end (true) or after each addition (false)
    public static final boolean COMPACT_MDD_ONLY_ONCE = Boolean.parseBoolean(properties.getProperty("COMPACT_MDD_ONLY_ONCE"));
}
