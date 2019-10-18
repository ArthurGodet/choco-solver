/*
@author Arthur Godet <arth.godet@gmail.com>
@since 14/10/2019
*/
package org.chocosolver.solver.constraints.nary;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.search.strategy.Search;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.tools.ArrayUtils;

import java.util.Arrays;
import java.util.Random;

public class Tmp {

    private static Random RAND = new Random(0);

    private static int generateNotNull(int bound) {
        int res;
        do {
            res = RAND.nextInt(bound);
        } while(res == 0);
        return res;
    }

    private static int[][] createInstance() {
        int w = 10+RAND.nextInt(10);
        int h = 10+RAND.nextInt(10);
        int n = generateNotNull(5);

        int[][] instance = new int[n+1][2];
        instance[0][0] = w;
        instance[0][1] = h;
        for(int i = 0; i<n; i++) {
            instance[i+1][0] = generateNotNull(w/2);
            instance[i+1][1] = generateNotNull(h/2);
        }

        for(int[] array : instance) {
            System.out.println(Arrays.toString(array));
        }

        return instance;
    }

    private static Model model(int[][] instance, int chocoModel) {
        Model model = new Model();
        int n = instance.length-1;
        int w = instance[0][0];
        int h = instance[0][1];
        IntVar[] x = new IntVar[n];
        IntVar[] y = new IntVar[x.length];
        IntVar[] dx = new IntVar[x.length];
        IntVar[] dy = new IntVar[x.length];
        for(int i = 0; i<x.length; i++) {
            x[i] = model.intVar("x["+i+"]", 0, w-instance[i+1][0]);
            y[i] = model.intVar("y["+i+"]", 0, h-instance[i+1][1]);
            dx[i] = model.intVar(instance[i+1][0]);
            dy[i] = model.intVar(instance[i+1][1]);
        }

        if(chocoModel == 0) {
            model.post(new Constraint("DIFFN", new PropDiffN(x, y, dx, dy, false), new PropDiffN(x, y, dx, dy, false)));
        } else if(chocoModel == 1) {
            model.post(new Constraint("DIFFN", new PropDiffNImproved(x, y, dx, dy, false)));
        } else {
            Propagator prop = new PropagDiffN(x, y, dx, dy, false);
            Propagator prop2 = new PropagDiffN(x, y, dx, dy, false);
            Propagator propInv = new PropagDiffN(y, x, dy, dx, false);
            Propagator propInv2 = new PropagDiffN(y, x, dy, dx, false);
            int xOffset = x[0].getUB()+dx[0].getValue();
            int yOffset = y[0].getUB()+dy[0].getValue();
            for(int i = 1; i<n; i++) {
                xOffset = Math.max(xOffset, x[i].getUB()+(dx[i].getValue()-1));
                yOffset = Math.max(yOffset, y[i].getUB()+(dy[i].getValue()-1));
            }
            IntVar[] oppX = new IntVar[n];
            IntVar[] oppY = new IntVar[n];
            for(int i = 0; i<n; i++) {
                oppX[i] = model.intOffsetView(model.intMinusView(x[i]), 1-dx[i].getValue()+xOffset);
                oppY[i] = model.intOffsetView(model.intMinusView(y[i]), 1-dy[i].getValue()+yOffset);
            }
            Propagator propOpp = new PropagDiffN(oppX, oppY, dx, dy, false); // TODO : is correct ???
            Propagator propOpp2 = new PropagDiffN(oppX, oppY, dx, dy, false); // TODO : is correct ???
            Propagator propOppInv = new PropagDiffN(oppY, oppX, dy, dx, false); // TODO : is correct ???
            Propagator propOppInv2 = new PropagDiffN(oppY, oppX, dy, dx, false); // TODO : is correct ???
            model.post(new Constraint("DIFFN", prop, prop2
                    ,propOpp, propOpp2
                    ,propInv, propInv2
                    ,propOppInv, propOppInv2
            ));
        }
        model.getSolver().setSearch(Search.inputOrderLBSearch(ArrayUtils.append(x,y)));
        return model;
    }

    public static boolean sameNumberOfSolutions(int[][] instance, boolean verbose) {
        Model chocoModel = model(instance, 0);
        Model chocoImprovedModel = model(instance, 1);
        Model diffnModel = model(instance, 2);

        while(chocoModel.getSolver().solve()) {}
        if(verbose) {
            System.out.println("nbSolutions;timeInMilliSeconds;nbNodes;nbFails");
            System.out.println("Choco model");
            System.out.println(chocoModel.getSolver().getSolutionCount()+";"
                    + chocoModel.getSolver().getTimeCountInNanoSeconds()/1000000+";"
                    + chocoModel.getSolver().getNodeCount()+";"
                    + chocoModel.getSolver().getFailCount());
            System.out.println("----------------");
        } else {
            System.out.println("chocoModel finished in "+(chocoModel.getSolver().getTimeCountInNanoSeconds()/1000000)+" ms !");
        }
        while(chocoImprovedModel.getSolver().solve()) {}
        if(verbose) {
            System.out.println("Choco improved model");
            System.out.println(chocoImprovedModel.getSolver().getSolutionCount()+";"
                    + chocoImprovedModel.getSolver().getTimeCountInNanoSeconds()/1000000+";"
                    + chocoImprovedModel.getSolver().getNodeCount()+";"
                    + chocoImprovedModel.getSolver().getFailCount());
            System.out.println("----------------");
        } else {
            System.out.println("chocoImprovedModel finished in "+(chocoImprovedModel.getSolver().getTimeCountInNanoSeconds()/1000000)+" ms !");
        }
        return chocoModel.getSolver().getSolutionCount() == chocoImprovedModel.getSolver().getSolutionCount();
//        while(diffnModel.getSolver().solve()) {}
//        if(verbose) {
//            System.out.println("DiffN model");
//            System.out.println(diffnModel.getSolver().getSolutionCount()+";"
//                    + diffnModel.getSolver().getTimeCountInNanoSeconds()/1000000+";"
//                    + diffnModel.getSolver().getNodeCount()+";"
//                    + diffnModel.getSolver().getFailCount());
//            System.out.println("----------------");
//        } else {
//            System.out.println("diffnModel finished in "+(diffnModel.getSolver().getTimeCountInNanoSeconds()/1000000)+" ms !");
//        }
//        return chocoModel.getSolver().getSolutionCount() == diffnModel.getSolver().getSolutionCount();
    }

    public static void main(String[] args) throws ContradictionException {
        int w = 4;
        int h = 5;
        int[][] instance = new int[][] {
                new int[]{w,h},
                new int[]{2,3},
                new int[]{1,5},
                new int[]{3,2},
                new int[]{1,3}
        };

//        x[0].instantiateTo(1, Cause.Null);
//        y[0].instantiateTo(0, Cause.Null);
//        x[1].instantiateTo(0, Cause.Null);
//        y[1].instantiateTo(0, Cause.Null);
//        x[2].instantiateTo(1, Cause.Null);
//        y[2].instantiateTo(3, Cause.Null);
//        x[3].instantiateTo(3, Cause.Null);
//        y[3].instantiateTo(0, Cause.Null);

        System.out.println(sameNumberOfSolutions(instance, true));
        System.out.println("----------------------------------------------------------------");

        boolean ok;
        do {
            int[][] inst = createInstance();
            System.out.println("size : "+(inst.length-1));
            ok = sameNumberOfSolutions(inst, true);
            System.out.println(ok);
            System.out.println("----------------------------------------------------------------");
        } while(ok);
    }
}
