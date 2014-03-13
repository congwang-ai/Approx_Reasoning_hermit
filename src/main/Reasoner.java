package main;

import io.*;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.*;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import visitor.*;

public class Reasoner {

	protected OWLOntologyManager manager;
	protected OWLOntology root_ontology;
	protected OWLOntology ontology;
	protected OWL2Normalization normalizer;
	protected OWL2Approximation approximation;
	protected OWL2ApproximationSC approximationSC;
	
	public Reasoner(OWLOntology ont) {
		this.root_ontology = ont;
	}

	public Reasoner(File file) throws OWLOntologyCreationException {
		this.manager = OWLManager.createOWLOntologyManager();
		root_ontology = manager.loadOntologyFromOntologyDocument(file);
	}

	public Reasoner(String file) throws OWLOntologyCreationException {
		this.manager = OWLManager.createOWLOntologyManager();
		root_ontology = manager
				.loadOntologyFromOntologyDocument(new File(file));
	}

	public void processInputOntology() throws OWLOntologyCreationException, IOException {

		long timeNormalization = System.currentTimeMillis();

		// -- Normalisation ------------
		normalizer = new OWL2Normalization(root_ontology);
		Set<OWLAxiom> normalizedAxioms = new HashSet<OWLAxiom>();

		// only for test
		Set<OWLAxiom> AxiomsSet = new HashSet<OWLAxiom>();

		ELKAxiomVisitor ELKVisitor = new ELKAxiomVisitor();

		for (OWLAxiom ax : root_ontology.getTBoxAxioms(true)) {

			ax.accept(ELKVisitor);

			if (!ELKVisitor.isInFragment()) {
				// Not in EL, then normalize it and approximate it		
				Set<OWLAxiom> nor_Axioms = normalizer.getNormalizedAxiom(ax);
				for(OWLAxiom ax_cur : nor_Axioms){
					ax_cur.accept(ELKVisitor);
					if(!ELKVisitor.isInFragment()){
						OWLAxiom approx_ax = approximation.getApproxAxioms(ax_cur);
						AxiomsSet.add(approx_ax);
					}else{
						AxiomsSet.add(ax_cur);
					}						
				}				
			} else {
				AxiomsSet.add(ax);
			}
		}
		
		

		// -- End Normalisation -----------------
		timeNormalization = System.currentTimeMillis() - timeNormalization;
		LogOutput.print("Normalisation took " + timeNormalization
				+ " milliseconds");

		// for(OWLAxiom axiom : normalizedAxioms)
		// System.out.println(axiom);

		/**
		OutputStream fos = new FileOutputStream(new File("output3.txt"));

		StringBuffer sb = new StringBuffer();
		for (OWLAxiom axiom : nonELKAxioms){
			sb.append(axiom.toString()+"\n");
			sb.append("\n------------------------------------------\n");
			for(OWLAxiom axiom_nor : normalizer.getNormalizedAxiom(axiom)){
				sb.append(axiom_nor.toString()+"\n");
			}
			break;
		}

		

		fos.write(sb.toString().getBytes());
		fos.close();

		normalizedAxioms.clear();
		
		*/

		// LogOutput.print("Signature normalized: "+
		// ontology.getSignature().size());

	}

}
