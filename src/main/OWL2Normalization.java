package main;

import java.util.*;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAnnotationAssertionAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLAsymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLAxiomVisitor;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLDatatypeDefinitionAxiom;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointUnionAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalDataPropertyAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLHasKeyAxiom;
import org.semanticweb.owlapi.model.OWLImportsDeclaration;
import org.semanticweb.owlapi.model.OWLInverseFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLInverseObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLIrreflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLNegativeDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLNegativeObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectExactCardinality;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLReflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom;
import org.semanticweb.owlapi.model.OWLSubAnnotationPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubDataPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.OWLSymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.RemoveAxiom;
import org.semanticweb.owlapi.model.SWRLRule;

import visitor.*;

public class OWL2Normalization {

	protected final OWLDataFactory m_factory;
	protected OWLOntology ontology;
	protected OWLOntologyManager m_manager;

	public OWL2Normalization(OWLOntology ontology) {
		m_manager = ontology.getOWLOntologyManager();
		m_factory = ontology.getOWLOntologyManager().getOWLDataFactory();
	}

	// Only Tbox, Rbox will be done by approximation step.
	// Need to consider

	public String getFreshName(OWLClassExpression e) {
		return "Aux_" + e.hashCode();
	}

	public Set<OWLAxiom> getNormalizedAxiom(OWLAxiom axiom) {
		Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
		List<OWLClassExpression[]> m_classExpressionInclusions = processAxioms(axiom);
		// RemoveAxiom removeAxiom = new RemoveAxiom(ontology, axiom);
		// m_manager.applyChange(removeAxiom);
		while (!m_classExpressionInclusions.isEmpty()) {
			OWLClassExpression[] current = m_classExpressionInclusions
					.remove(m_classExpressionInclusions.size() - 1);
			OWLClassExpression left = current[0];
			OWLClassExpression right = current[1];
			if (isObjectExpressionSimple(left, right)) {
				axioms.add(m_factory.getOWLSubClassOfAxiom(left, right));
			} else {
				if (!isLeftSimple(left)) {
					// left is Unionof
					if (left instanceof OWLObjectUnionOf) {
						List<OWLClassExpression> disjuncts = ((OWLObjectUnionOf) current[0])
								.getOperandsAsList();
						for (OWLClassExpression e : disjuncts) {
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { e, right });
						}
					} else if (current[0] instanceof OWLObjectIntersectionOf) {
						List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) current[0])
								.getOperandsAsList();
						if (conjuncts.size() > 2) {
							OWLObjectIntersectionOf newConjunct = m_factory
									.getOWLObjectIntersectionOf(
											conjuncts.remove(0), conjuncts.remove(1));
							//freshname is the newConjunct
							OWLClass aux_concept = m_factory.getOWLClass(IRI
									.create(getFreshName(newConjunct)));
							m_classExpressionInclusions
									.add(new OWLClassExpression[] {
											newConjunct, aux_concept });
							Set<OWLClassExpression> newconjuncts = new HashSet<OWLClassExpression>();
							conjuncts.add(0, aux_concept);
							newconjuncts.addAll(conjuncts);
							OWLObjectIntersectionOf newConjunctEx = m_factory
									.getOWLObjectIntersectionOf(newconjuncts);
							m_classExpressionInclusions
									.add(new OWLClassExpression[] {
											newConjunctEx, right });
						}
						if (conjuncts.size() == 2) {
							if (!isSimpleConcept(conjuncts.get(0))) {
								OWLClass aux_concept = m_factory
										.getOWLClass(IRI.create(getFreshName(conjuncts.get(0))));
								m_classExpressionInclusions
										.add(new OWLClassExpression[] {
												conjuncts.get(0), aux_concept });
								OWLObjectIntersectionOf newConjunctEx = m_factory
										.getOWLObjectIntersectionOf(
												aux_concept, conjuncts.get(1));
								m_classExpressionInclusions
										.add(new OWLClassExpression[] {
												newConjunctEx, right });
							} else if (!isSimpleConcept(conjuncts.get(1))) {
								OWLClass aux_concept = m_factory
										.getOWLClass(IRI.create(getFreshName(conjuncts.get(1))));
								m_classExpressionInclusions
										.add(new OWLClassExpression[] {
												conjuncts.get(1), aux_concept });
								OWLObjectIntersectionOf newConjunctEx = m_factory
										.getOWLObjectIntersectionOf(
												conjuncts.get(0), aux_concept);
								m_classExpressionInclusions
										.add(new OWLClassExpression[] {
												newConjunctEx, right });
							}
						}
					}
					// left is \exists R.C Havn't considered complex Role
					else if (left instanceof OWLObjectSomeValuesFrom) {
						if (!isObjectSomeValuesFromSimple(left)) {
							OWLClassExpression original = ((OWLObjectSomeValuesFrom) current[0])
									.getFiller();
							OWLClass aux_concept = m_factory.getOWLClass(IRI
									.create(getFreshName(original)));
							OWLObjectPropertyExpression theProperty = ((OWLObjectSomeValuesFrom) current[0])
									.getProperty();
							OWLObjectSomeValuesFrom newExpression = m_factory
									.getOWLObjectSomeValuesFrom(theProperty,
											aux_concept);
							m_classExpressionInclusions
									.add(new OWLClassExpression[] {
											newExpression, right });
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { original,
											aux_concept });
						}
						// left is \forall R.C
					} else if (current[0] instanceof OWLObjectAllValuesFrom) {
						if (!isObjectAllValuesFromSimple(current[0])) {
							OWLClassExpression original = ((OWLObjectAllValuesFrom) current[0])
									.getFiller();
							OWLClass aux_concept = m_factory.getOWLClass(IRI
									.create(getFreshName(original)));
							OWLObjectPropertyExpression theProperty = ((OWLObjectAllValuesFrom) current[0])
									.getProperty();
							OWLObjectAllValuesFrom newExpression = m_factory
									.getOWLObjectAllValuesFrom(theProperty,
											aux_concept);
							m_classExpressionInclusions
									.add(new OWLClassExpression[] {
											newExpression, right });
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { original,
											aux_concept });
						}
						// left is \exists >=n R.C
					} else if (current[0] instanceof OWLObjectMinCardinality) {
						if (!isObjectMinCardinalitySimple(current[0])) {
							OWLClassExpression original = ((OWLObjectMinCardinality) current[0])
									.getFiller();
							OWLClass freshname = m_factory.getOWLClass(IRI
									.create(getFreshName(original)));
							OWLObjectPropertyExpression theProperty = ((OWLObjectMinCardinality) current[0])
									.getProperty();
							int cardinality = ((OWLObjectMinCardinality) current[0])
									.getCardinality();
							OWLObjectMinCardinality newExpression = m_factory
									.getOWLObjectMinCardinality(cardinality,
											theProperty, freshname);
							m_classExpressionInclusions
									.add(new OWLClassExpression[] {
											newExpression, current[1] });
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { original,
											freshname });
						}
						// left is \exists <=n R.C
					} else if (current[0] instanceof OWLObjectMaxCardinality) {
						if (!isObjectMaxCardinalitySimple(current[0])) {
							OWLClassExpression original = ((OWLObjectMaxCardinality) current[0])
									.getFiller();
							OWLClass freshname = m_factory.getOWLClass(IRI
									.create(getFreshName(original)));
							OWLObjectPropertyExpression theProperty = ((OWLObjectMaxCardinality) current[0])
									.getProperty();
							int cardinality = ((OWLObjectMaxCardinality) current[0])
									.getCardinality();
							OWLObjectMaxCardinality newExpression = m_factory
									.getOWLObjectMaxCardinality(cardinality,
											theProperty, freshname);
							m_classExpressionInclusions
									.add(new OWLClassExpression[] {
											newExpression, current[1] });
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { original,
											freshname });
						}
					} else if (current[0] instanceof OWLObjectExactCardinality) {
						OWLClassExpression original = ((OWLObjectExactCardinality) current[0])
								.getFiller();
						OWLObjectPropertyExpression theProperty = ((OWLObjectMaxCardinality) current[0])
								.getProperty();
						int cardinality = ((OWLObjectExactCardinality) current[0])
								.getCardinality();
						OWLObjectMaxCardinality maxExpression = m_factory
								.getOWLObjectMaxCardinality(cardinality,
										theProperty, original);
						OWLObjectMaxCardinality minExpression = m_factory
								.getOWLObjectMaxCardinality(cardinality,
										theProperty, original);
						OWLObjectIntersectionOf conjuncts = m_factory
								.getOWLObjectIntersectionOf(maxExpression,
										minExpression);
						m_classExpressionInclusions
								.add(new OWLClassExpression[] { conjuncts,
										current[1] });
					}
					// right is not simple
				} else if (!isRightSimple(current[1])) {
					if (current[1] instanceof OWLObjectSomeValuesFrom) {
						OWLClassExpression original = ((OWLObjectSomeValuesFrom) current[1])
								.getFiller();
						OWLClass freshname = m_factory.getOWLClass(IRI
								.create(getFreshName(original)));
						OWLObjectPropertyExpression theProperty = ((OWLObjectSomeValuesFrom) current[1])
								.getProperty();
						OWLObjectSomeValuesFrom newExpression = m_factory
								.getOWLObjectSomeValuesFrom(theProperty,
										freshname);
						m_classExpressionInclusions
								.add(new OWLClassExpression[] { current[0],
										newExpression });
						m_classExpressionInclusions
								.add(new OWLClassExpression[] { freshname,
										original });
					} else if (current[1] instanceof OWLObjectAllValuesFrom) {
						OWLClassExpression original = ((OWLObjectAllValuesFrom) current[1])
								.getFiller();
						OWLClass freshname = m_factory.getOWLClass(IRI
								.create(getFreshName(original)));
						OWLObjectPropertyExpression theProperty = ((OWLObjectAllValuesFrom) current[1])
								.getProperty();
						OWLObjectAllValuesFrom newExpression = m_factory
								.getOWLObjectAllValuesFrom(theProperty,
										freshname);
						m_classExpressionInclusions
								.add(new OWLClassExpression[] { current[0],
										newExpression });
						m_classExpressionInclusions
								.add(new OWLClassExpression[] { freshname,
										original });
					} else if (current[1] instanceof OWLObjectMaxCardinality) {
						if (!isObjectMaxCardinalitySimple(current[1])) {
							OWLClassExpression original = ((OWLObjectMaxCardinality) current[1])
									.getFiller();
							OWLClass freshname = m_factory.getOWLClass(IRI
									.create(getFreshName(original)));
							OWLObjectPropertyExpression theProperty = ((OWLObjectMaxCardinality) current[1])
									.getProperty();
							int cardinality = ((OWLObjectMaxCardinality) current[1])
									.getCardinality();
							OWLObjectMaxCardinality newExpression = m_factory
									.getOWLObjectMaxCardinality(cardinality,
											theProperty, freshname);
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { current[0],
											newExpression });
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { freshname,
											original });
						}
					} else if (current[1] instanceof OWLObjectMinCardinality) {
						if (!isObjectMinCardinalitySimple(current[1])) {
							OWLClassExpression original = ((OWLObjectMinCardinality) current[1])
									.getFiller();
							OWLClass freshname = m_factory.getOWLClass(IRI
									.create(getFreshName(original)));
							OWLObjectPropertyExpression theProperty = ((OWLObjectMinCardinality) current[1])
									.getProperty();
							int cardinality = ((OWLObjectMinCardinality) current[1])
									.getCardinality();
							OWLObjectMinCardinality newExpression = m_factory
									.getOWLObjectMinCardinality(cardinality,
											theProperty, freshname);
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { current[0],
											newExpression });
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { freshname,
											original });
						}
					} else if (current[1] instanceof OWLObjectExactCardinality) {
						OWLClassExpression original = ((OWLObjectExactCardinality) current[1])
								.getFiller();
						OWLObjectPropertyExpression theProperty = ((OWLObjectMaxCardinality) current[1])
								.getProperty();
						int cardinality = ((OWLObjectExactCardinality) current[1])
								.getCardinality();
						OWLObjectMaxCardinality maxExpression = m_factory
								.getOWLObjectMaxCardinality(cardinality,
										theProperty, original);
						OWLObjectMaxCardinality minExpression = m_factory
								.getOWLObjectMaxCardinality(cardinality,
										theProperty, original);
						m_classExpressionInclusions
								.add(new OWLClassExpression[] { current[0],
										maxExpression });
						m_classExpressionInclusions
								.add(new OWLClassExpression[] { current[0],
										minExpression });
					} else if (current[1] instanceof OWLObjectIntersectionOf) {
						List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) current[1])
								.getOperandsAsList();
						for (int i = 0; i < conjuncts.size(); i++) {
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { current[0],
											conjuncts.get(i) });
						}
						// 这里有点问题。。 少东西
					} else if (current[1] instanceof OWLObjectUnionOf) {
						List<OWLClassExpression> disjuncts = ((OWLObjectUnionOf) current[1])
								.getOperandsAsList();
						if (disjuncts.size() > 2) { // when conjunctions
													// are
													// more than 2
							OWLObjectUnionOf newDisjunct = m_factory
									.getOWLObjectUnionOf(disjuncts.remove(0),
											disjuncts.remove(1));
							OWLClass freshname = m_factory.getOWLClass(IRI
									.create(getFreshName(newDisjunct)));
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { freshname,
											newDisjunct });
							disjuncts.add(0, freshname);
							OWLObjectUnionOf newDisjunctEx = m_factory
									.getOWLObjectUnionOf(new HashSet<OWLClassExpression>(
											disjuncts));
							m_classExpressionInclusions
									.add(new OWLClassExpression[] { current[0],
											newDisjunctEx });
						} else { // when disjunctions are 2
							if (!isSimpleConcept(disjuncts.get(0))) {
								OWLClass freshname = m_factory
										.getOWLClass(IRI
												.create(getFreshName(disjuncts
														.get(0))));
								m_classExpressionInclusions
										.add(new OWLClassExpression[] {
												freshname, disjuncts.get(0) });
								OWLObjectUnionOf newDisjunctEx = m_factory
										.getOWLObjectUnionOf(freshname,
												disjuncts.get(1));
								m_classExpressionInclusions
										.add(new OWLClassExpression[] {
												current[0], newDisjunctEx });
							} else if (!isSimpleConcept(disjuncts.get(1))) {
								OWLClass freshname = m_factory
										.getOWLClass(IRI
												.create(getFreshName(disjuncts
														.get(1))));
								m_classExpressionInclusions
										.add(new OWLClassExpression[] {
												freshname, disjuncts.get(1) });
								OWLObjectUnionOf newDisjunctEx = m_factory
										.getOWLObjectUnionOf(freshname,
												disjuncts.get(0));
								m_classExpressionInclusions
										.add(new OWLClassExpression[] {
												current[0], newDisjunctEx });
							} else {
								m_classExpressionInclusions
										.add(new OWLClassExpression[] {
												current[0], current[1] });
							}
						}
					}
				}

			}
		}
		return axioms;
	}

	// 有问题，这里处理全部了，应该分着处理，更有效率, equivelence 可能也有问题，可能会生成两个新的auxconcept

	public List<OWLClassExpression[]> processAxioms(OWLAxiom axiom) {
		AxiomVisitor axiomVisitor = new AxiomVisitor(m_factory);
		axiom.accept(axiomVisitor);
		return axiomVisitor.getInclusions();
	}

	// Atomic Concept or Negation of Atomic Concept or Individuals.
	private boolean isSimpleConcept(OWLClassExpression concept) {
		if (concept instanceof OWLClass) {
			return true;
		} else if (concept instanceof OWLObjectOneOf) {
			return true;
		} else if (concept instanceof OWLObjectComplementOf) {
			if (isSimpleConcept(concept.getComplementNNF())) {
				return true;
			}
		}
		return false;
	}

	// property might be inverse, at this point
	private boolean isObjectSomeValuesFromSimple(OWLClassExpression ex) {
		if (isSimpleConcept(((OWLObjectSomeValuesFrom) ex).getFiller())) {
			return true;
		}
		return false;
	}

	// property might be inverse, at this point
	private boolean isObjectAllValuesFromSimple(OWLClassExpression ex) {
		if (isSimpleConcept(((OWLObjectAllValuesFrom) ex).getFiller())) {
			return true;
		}
		return false;
	}

	// property might be inverse, at this point
	private boolean isObjectMaxCardinalitySimple(OWLClassExpression ex) {
		if (isSimpleConcept(((OWLObjectMaxCardinality) ex).getFiller())) {
			return true;
		}
		return false;
	}

	// property might be inverse, at this point
	private boolean isObjectMinCardinalitySimple(OWLClassExpression ex) {
		if (isSimpleConcept(((OWLObjectMinCardinality) ex).getFiller())) {
			return true;
		}
		return false;
	}

	private boolean isObjectExpressionSimple(OWLClassExpression left,
			OWLClassExpression right) {
		if (isSimpleConcept(left)) {
			// both sides are simple
			if (isSimpleConcept(right))
				return true;
			// A \subclass \exists R.C
			else if (right instanceof OWLObjectSomeValuesFrom) {
				return isObjectSomeValuesFromSimple(right);
			} else if (right.isOWLThing() || right.isOWLNothing())
				return true;
			// A \subclass \exists R.Self
			else if (right instanceof OWLObjectHasSelf)
				return true;
			// A \subclass \forall R.C
			else if (right instanceof OWLObjectAllValuesFrom) {
				return isObjectAllValuesFromSimple(right);
			}
			// A \subclass B or C
			else if (right instanceof OWLObjectUnionOf) {
				List<OWLClassExpression> disjuncts = ((OWLObjectUnionOf) right)
						.getOperandsAsList();
				if (disjuncts.size() != 2)
					return false;
				for (int i = 0; i < 2; i++) {
					if (!isSimpleConcept(disjuncts.get(i))) {
						return false;
					}
				}
				return true;
				// A \subclass <=n R.C
			} else if (right instanceof OWLObjectMaxCardinality) {
				return isObjectMaxCardinalitySimple(right);
				// A \subclass >= n R.C
			} else if (right instanceof OWLObjectMinCardinality) {
				return isObjectMinCardinalitySimple(right);
			} else
				return false;
		}
		if (isSimpleConcept(right)) {
			if (left instanceof OWLObjectIntersectionOf) {
				if (!isSimpleConcept(right))
					return false;
				List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) left)
						.getOperandsAsList();
				if (conjuncts.size() != 2)
					return false;
				for (int i = 0; i < 2; i++) {
					if (!isSimpleConcept(conjuncts.get(i))) {
						return false;
					}
				}
				return true;
				// \exists R.A \subclass C
			} else if (left instanceof OWLObjectSomeValuesFrom) {
				return isObjectSomeValuesFromSimple(left);
				// \forall R.A \subclass C
			} else if (left instanceof OWLObjectAllValuesFrom) {
				return isObjectAllValuesFromSimple(left);
				// \top \subclass C
			} else if (left.isOWLThing() || left.isOWLThing())
				return true;
			// \exists R.self \subclass C
			else if (left instanceof OWLObjectHasSelf)
				return true;
			// <= n R.A \subclass C
			else if (left instanceof OWLObjectMaxCardinality) {
				return isObjectMaxCardinalitySimple(left);
			}
			// >= n R.A \subclass C
			else if (left instanceof OWLObjectMinCardinality)
				return isObjectMinCardinalitySimple(left);
			else
				return false;
		}
		return false;
	}

	public boolean isLeftSimple(OWLClassExpression left) {
		if (isSimpleConcept(left) || left.isOWLThing() || left.isOWLThing()) {
			return true;
		} else if (left instanceof OWLObjectIntersectionOf) {
			List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) left)
					.getOperandsAsList();
			if (conjuncts.size() != 2)
				return false;
			for (int i = 0; i < 2; i++) {
				if (!isSimpleConcept(conjuncts.get(i))) {
					return false;
				}
			}
			return true;
		} else if (left instanceof OWLObjectSomeValuesFrom) {
			return isSimpleConcept(((OWLObjectSomeValuesFrom) left).getFiller());
		} else if (left instanceof OWLObjectAllValuesFrom) {
			return isSimpleConcept(((OWLObjectAllValuesFrom) left).getFiller());
		} else if (left instanceof OWLObjectMinCardinality) {
			return isSimpleConcept(((OWLObjectMinCardinality) left).getFiller());
		} else if (left instanceof OWLObjectMaxCardinality) {
			return isSimpleConcept(((OWLObjectMaxCardinality) left).getFiller());
		} else if (left instanceof OWLObjectHasSelf)
			return true;
		else
			return false;
	}

	public boolean isRightSimple(OWLClassExpression right) {
		if (isSimpleConcept(right) || right.isOWLNothing()
				|| right.isOWLThing()) {
			return true;
		} else if (right instanceof OWLObjectSomeValuesFrom) {
			return isSimpleConcept(((OWLObjectSomeValuesFrom) right)
					.getFiller());
		} else if (right instanceof OWLObjectAllValuesFrom) {
			return isSimpleConcept(((OWLObjectAllValuesFrom) right).getFiller());
		} else if (right instanceof OWLObjectMaxCardinality) {
			return isSimpleConcept(((OWLObjectMaxCardinality) right)
					.getFiller());
		} else if (right instanceof OWLObjectMinCardinality) {
			return isSimpleConcept(((OWLObjectMinCardinality) right)
					.getFiller());
		} else if (right instanceof OWLObjectUnionOf) {
			List<OWLClassExpression> disjuncts = ((OWLObjectUnionOf) right)
					.getOperandsAsList();
			if (disjuncts.size() != 2)
				return false;
			for (int i = 0; i < 2; i++) {
				if (!isSimpleConcept(disjuncts.get(i))) {
					return false;
				}
			}
			return true;
		} else if (right instanceof OWLObjectHasSelf)
			return true;
		else
			return false;
	}

}
