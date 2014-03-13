package test;

import main.Reasoner;

import org.semanticweb.owlapi.apibinding.OWLManager;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

public class pizzaOnt_simple_test {

	public static void main(String[] args) throws Exception {
		
		Reasoner  r = new Reasoner("test.owl");
		r.processInputOntology();
	} 
}
