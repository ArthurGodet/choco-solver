/*
 * This file is part of choco-parsers, http://choco-solver.org/
 *
 * Copyright (c) 2019, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.parser.json;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.RealVar;
import org.testng.annotations.Test;

/**
 *
 * <p>
 * Project: choco-json.
 * @author Charles Prud'homme
 * @since 27/09/2017.
 */
public class JSONRealConstraintTest extends JSONConstraintTest{

    @Test(groups="ibex", timeOut=60000)
    public void testRealCstr(){
        Model model = new Model();
        RealVar x = model.realVar(0., 1.2, 1.E-1);
        RealVar y = model.realVar(.8, 2.2, 1.E-1);
        model.realIbexGenericConstraint(
                "{0}^2+{1}^2<=1;", x, y
        ).post();
        model.realIbexGenericConstraint(
                "{0} < {1}", x, y
        ).post();
        eval(model, false);
    }

    @Test(groups="ibex", timeOut=60000)
    public void testRealCstr2(){
        Model model = new Model();
        RealVar x = model.realVar(0., 1.2, 1.E-1);
        RealVar y = model.realVar(.8, 2.2, 1.E-1);
        BoolVar b = model.boolVar();
        model.realIbexGenericConstraint(
                "{0} < {1}", x, y
        ).reifyWith(b);
        eval(model, false);
    }

    @Test(groups="ibex", timeOut=60000)
    public void testRealCstr3(){
        Model model = new Model();
        RealVar x = model.realVar(0., 1.2, 1.E-1);
        RealVar y = model.realVar(.8, 2.2, 1.E-1);
        model.realIbexGenericConstraint(
                "{0}^2+{1}^2<=1;{0} < {1}", x, y
        ).post();
        eval(model, true);
    }

    @Test(groups="ibex", timeOut=60000)
    public void testRealCstr4(){
        Model model = new Model();
        RealVar x = model.realVar(.8, 1.2, 1.E-1);
        RealVar y = model.realVar(.8, 2.2, 1.E-1);
        BoolVar b = model.boolVar();
        model.realIbexGenericConstraint(
                "{0}^2+{1}^2<=1;{0} < {1}", x, y
        ).reifyWith(b);
        eval(model, true);
    }
}

