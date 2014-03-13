package test;

import static org.junit.Assert.*;

import org.junit.Test;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;

public class Normalization_Test {

	public static void owlPrimer() throws OWLOntologyCreationException,
			OWLOntologyStorageException {

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		IRI ontologyIRI = IRI.create("http://example.com/owlapi/dummy");
		OWLOntology ont = manager.createOntology(ontologyIRI);
		OWLDataFactory factory = manager.getOWLDataFactory();
	}

	@Test
	public void testConjunctions() {
		
	}
}
