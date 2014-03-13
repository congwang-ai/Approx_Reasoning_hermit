package storage;

import java.util.*;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;

public class axiomsStorage {

	public final HashMap<OWLClass, OWLClass> c_to_n;
	public Set<OWLClass> negation_set = new HashSet<OWLClass>();
	
	public axiomsStorage(){
		c_to_n = new HashMap<OWLClass, OWLClass>();
	}
	
	public void putNegationMap(OWLClass c, OWLClass negC){
		if(!c_to_n.containsKey(c)){
			c_to_n.put(c, negC);
		}
	}
	
	public boolean hasNegation(OWLClass c){
		return negation_set.contains(c);
	}
	
	public void putNegation(OWLClass c){
		if(!negation_set.contains(c))
			negation_set.add(c);
	}
	
}
