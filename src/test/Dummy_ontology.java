package test;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLXMLOntologyFormat;
import org.semanticweb.owlapi.io.StreamDocumentTarget;
import org.semanticweb.owlapi.model.*;

public class Dummy_ontology {

	public static void owlPrimer() throws OWLOntologyCreationException,
			OWLOntologyStorageException {

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		IRI ontologyIRI = IRI.create("http://example.com/owlapi/dummy");
		OWLOntology ont = manager.createOntology(ontologyIRI);
		OWLDataFactory factory = manager.getOWLDataFactory();

		OWLClass concept_A = factory
				.getOWLClass(IRI.create(ontologyIRI + "#A"));
		OWLClass concept_B = factory
				.getOWLClass(IRI.create(ontologyIRI + "#B"));
		OWLClass concept_C = factory
				.getOWLClass(IRI.create(ontologyIRI + "#C"));
		OWLClass concept_D = factory
				.getOWLClass(IRI.create(ontologyIRI + "#D"));

		OWLObjectProperty hasWife = factory.getOWLObjectProperty(IRI
				.create(ontologyIRI + "#R"));

		OWLObjectIntersectionOf conjunct1 = factory.getOWLObjectIntersectionOf(
				concept_A, concept_B);

		OWLObjectIntersectionOf conjunct2 = factory.getOWLObjectIntersectionOf(
				conjunct1, concept_C);

		OWLAxiom axiom1 = factory.getOWLSubClassOfAxiom(conjunct2, concept_D);

		AddAxiom addAxiom1 = new AddAxiom(ont, axiom1);

		manager.applyChange(addAxiom1);

		manager.saveOntology(ont, new OWLXMLOntologyFormat(),
				new StreamDocumentTarget(System.out));

	}

	public static void main(String[] args) throws OWLOntologyCreationException,
			OWLOntologyStorageException {
		owlPrimer();
	}
}
