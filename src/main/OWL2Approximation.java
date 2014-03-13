package main;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

import storage.OWLAxioms;
import storage.axiomsStorage;

//不清楚是不是每个concept，都必须要加 \neg concept \conjunct concept -> \bot
//不清楚是不是每个axiom，都必须改写成 neg A \sub neg C

public class OWL2Approximation {

	// protected final OWLAxioms m_axioms;
	protected final OWLDataFactory m_factory;
	public HashMap<OWLClass, OWLClass> c_to_n;
	public HashMap<OWLClass, OWLClass> n_to_c;
	public Set<OWLClass> m_named_classes;
	public Set<OWLClass> negation_set;
	public Set<OWLAxiom> extra_axioms;

	//static private axiomsStorage store = new axiomsStorage();

	public OWL2Approximation(OWLOntology ontology) {
		m_factory = ontology.getOWLOntologyManager().getOWLDataFactory();
		m_named_classes.addAll(ontology.getClassesInSignature(true));
		c_to_n = new HashMap<OWLClass, OWLClass>();
		n_to_c = new HashMap<OWLClass, OWLClass>();
		negation_set = new HashSet<OWLClass>();
		extra_axioms = new HashSet<OWLAxiom>();
	}

	public void buildMapping() {
		for (OWLClass e : m_named_classes) {
			String negName = "internal_negated_" + e.getIRI().getFragment();
			OWLClass negConcept = m_factory.getOWLClass(IRI.create(negName));
			negation_set.add(negConcept);
			c_to_n.put(e, negConcept);
			n_to_c.put(negConcept, e);
			OWLObjectIntersectionOf newConjunctEx = m_factory
					.getOWLObjectIntersectionOf(e, negConcept);
			extra_axioms.add(m_factory.getOWLSubClassOfAxiom(newConjunctEx,
					m_factory.getOWLNothing()));
		}
	}

	public OWLAxiom getApproxAxioms(OWLAxiom ax) {
		buildMapping();
		OWLClassExpression[] exprs = getExpressions(ax);		
		return removeNegation(exprs);
	}

	private OWLAxiom removeNegation(OWLClassExpression[] exprs) {
		OWLClassExpression left = removeNegation(exprs[0]);
		OWLClassExpression right = removeNegation(exprs[0]);
		return m_factory.getOWLSubClassOfAxiom(left, right);
	}

	private OWLClassExpression removeNegation(OWLClassExpression ex) {
		if (ex instanceof OWLObjectComplementOf) {
			return c_to_n.get(ex.getComplementNNF());
		} else if (ex instanceof OWLClass) {
			return ex;
		} else if (ex.isOWLThing()) {
			return ex;
		} else if (ex.isOWLNothing()) {
			return ex;
		} else if (ex instanceof OWLObjectSomeValuesFrom) {
			if (((OWLObjectSomeValuesFrom) ex).getFiller() instanceof OWLObjectComplementOf) {
				return m_factory.getOWLObjectSomeValuesFrom(
						((OWLObjectSomeValuesFrom) ex).getProperty(), c_to_n
								.get(((OWLObjectSomeValuesFrom) ex).getFiller()
										.getComplementNNF()));
			} else if (((OWLObjectSomeValuesFrom) ex).getFiller() instanceof OWLClass) {
				return ex;
			}
		} else if (ex instanceof OWLObjectAllValuesFrom) {
			if (((OWLObjectAllValuesFrom) ex).getFiller() instanceof OWLObjectComplementOf) {
				return m_factory.getOWLObjectAllValuesFrom(
						((OWLObjectAllValuesFrom) ex).getProperty(), c_to_n
								.get(((OWLObjectAllValuesFrom) ex).getFiller()
										.getComplementNNF()));
			} else if (((OWLObjectAllValuesFrom) ex).getFiller() instanceof OWLClass) {
				return ex;
			}
		} else if (ex instanceof OWLObjectIntersectionOf) {
			List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) ex)
					.getOperandsAsList();
			OWLClassExpression ex0 = removeNegation(conjuncts.get(0));
			OWLClassExpression ex1 = removeNegation(conjuncts.get(1));
			return m_factory.getOWLObjectIntersectionOf(ex0, ex1);
		} else if (ex instanceof OWLObjectUnionOf) {
			List<OWLClassExpression> conjuncts = ((OWLObjectUnionOf) ex)
					.getOperandsAsList();
			OWLClassExpression ex0 = removeNegation(conjuncts.get(0));
			OWLClassExpression ex1 = removeNegation(conjuncts.get(1));
			return m_factory.getOWLObjectUnionOf(ex0, ex1);
		} else if (ex instanceof OWLObjectMinCardinality) {
			if (((OWLObjectMinCardinality) ex).getFiller() instanceof OWLObjectComplementOf) {
				return m_factory.getOWLObjectMinCardinality(
						((OWLObjectMinCardinality) ex).getCardinality(),
						((OWLObjectMinCardinality) ex).getProperty(), c_to_n
								.get(((OWLObjectMinCardinality) ex).getFiller()
										.getComplementNNF()));
			} else if (((OWLObjectMinCardinality) ex).getFiller() instanceof OWLClass) {
				return ex;
			}
		} else if (ex instanceof OWLObjectMaxCardinality) {
			if (((OWLObjectMaxCardinality) ex).getFiller() instanceof OWLObjectComplementOf) {
				return m_factory.getOWLObjectMaxCardinality(
						((OWLObjectMaxCardinality) ex).getCardinality(),
						((OWLObjectMaxCardinality) ex).getProperty(), c_to_n
								.get(((OWLObjectMaxCardinality) ex).getFiller()
										.getComplementNNF()));
			} else if (((OWLObjectMaxCardinality) ex).getFiller() instanceof OWLClass) {
				return ex;
			}
		} else if (ex instanceof OWLObjectHasSelf) {
			return ex;
		}

		return ex;
	}

	private OWLClassExpression[] getExpressions(OWLAxiom ax) {
		assert (ax instanceof OWLSubClassOfAxiom);
		OWLClassExpression[] exprs = new OWLClassExpression[2];
		exprs[0] = ((OWLSubClassOfAxiom) ax).getSubClass().getNNF();
		exprs[1] = ((OWLSubClassOfAxiom) ax).getSuperClass().getNNF();
		return exprs;
	}
}
