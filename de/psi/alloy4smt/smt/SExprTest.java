package de.psi.alloy4smt.smt;

import org.junit.Test;

import static de.psi.alloy4smt.smt.SExpr.add;
import static de.psi.alloy4smt.smt.SExpr.num;
import static org.junit.Assert.assertEquals;

public class SExprTest {

    @Test
    public void simple() {
        SExpr e = add(num(3), num(4));
        assertEquals("(+ 3 4)", e.toString());
    }
}
