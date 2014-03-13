package test;

import java.io.File;

import org.semanticweb.more.MOReReasoner;
import org.semanticweb.more.OWL2ReasonerManager;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.InferenceType;

public class More_test {

	 public static void main(String[] args) throws Exception {
         
         OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
         OWLOntology ont;
                 
         //MORe accepts the same ontology formats as the OWL API: 
         //RDF/XML, OWL/XML, OWL Functional, OBO, KRSS, and Turtle (n3).
         //Loading ontology from file
         ont = manager.loadOntologyFromOntologyDocument(new File("path to ontology"));
         //or from URI
         ont = manager.loadOntology(IRI.create("onology uri"));
                 
         //Create MORe reasoner
         MOReReasoner MORe = new MOReReasoner(ont);
         
         //Setting JFact as OWL 2 reasoner
        // MORe.setReasoner(OWL2ReasonerManager.ELK);
         
         //Setting HermiT as OWL 2 reasoner
         MORe.setReasoner(OWL2ReasonerManager.HERMIT);                           
         
         //Classify the ontology
         MORe.precomputeInferences(InferenceType.CLASS_HIERARCHY);
         
         //Retrieves the set of unsatisfiable classes
         MORe.getUnsatisfiableClasses();
         
         //Terminates the reasoner
         MORe.dispose();
                                 
 }
	 
}
