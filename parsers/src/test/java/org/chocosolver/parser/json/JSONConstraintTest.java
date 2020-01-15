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
import org.testng.Assert;
import org.testng.annotations.DataProvider;

/**
 * <p> Project: choco-json.
 *
 * @author Charles Prud'homme
 * @since 12/09/2017.
 */
public class JSONConstraintTest {

    @DataProvider(name = "bool")
    protected static Object[][] bool() {
        return new Object[][]{
                {true},
                {false}
        };
    }

    @DataProvider(name = "sign")
    protected static Object[][] sign() {
        return new String[][]{
                {"="},
                {"!="},
                {">"},
                {">="},
                {"<"},
                {"<="},
        };
    }

    @SuppressWarnings("Duplicates")
    protected void eval(Model model, boolean mayDiffer) {
        String org = model.toString();
        String str = JSON.toString(model);
        System.out.printf("%s\n", str);
        Model cpy = JSON.fromString(str);
        System.out.printf("%s\n", cpy);
        if(!mayDiffer) {
            Assert.assertEquals(cpy.toString(), org);
        }
        long nsol = model.getSolver().findAllSolutions().size();
        long nsolc = cpy.getSolver().findAllSolutions().size();
        System.out.printf("Solutions: %d vs. %d\n", nsol, nsolc);
        Assert.assertEquals(nsolc, nsol, "wrong number of solutions");
    }

}