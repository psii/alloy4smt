package de.psi.alloy4smt.ast;

import edu.mit.csail.sdg.alloy4compiler.ast.Sig;

public class Helpers {

	public static Sig getSigByName(Iterable<Sig> sigs, String name) {
	    Sig result = null;
	    for (Sig s: sigs) {
	        if (s.toString().equals(name)) {
	            result = s;
	            break;
	        }
	    }
	    return result;
	}

	public static Sig.Field getFieldByName(Iterable<Sig.Field> fields, String name) {
	    Sig.Field result = null;
	    for (Sig.Field field: fields) {
	        if (field.label.equals(name)) {
	            result = field;
	            break;
	        }
	    }
	    return result;
	}

}
