package visitor;

import org.semanticweb.owlapi.model.OWLAxiomVisitor;

public interface OWLFragmentVisitor extends OWLAxiomVisitor{

	boolean isInFragment();
}
