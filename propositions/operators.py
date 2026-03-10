# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

# A dummy variable name used to replace constants
_DUMMY_VAR = 'p'

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        # Replace T with (p | ~p), F with (p & ~p)
        p = Formula(_DUMMY_VAR)
        if formula.root == 'T':
            return Formula('|', p, Formula('~', p))
        else:  # 'F'
            return Formula('&', p, Formula('~', p))
    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))
    # Binary operators
    left = to_not_and_or(formula.first)
    right = to_not_and_or(formula.second)
    if formula.root == '&':
        return Formula('&', left, right)
    if formula.root == '|':
        return Formula('|', left, right)
    if formula.root == '->':
        return Formula('|', Formula('~', left), right)
    if formula.root == '+':  # XOR
        return Formula('|',
                       Formula('&', left, Formula('~', right)),
                       Formula('&', Formula('~', left), right))
    if formula.root == '<->':  # equivalence
        return Formula('|',
                       Formula('&', left, right),
                       Formula('&', Formula('~', left), Formula('~', right)))
    if formula.root == '-&':  # NAND
        return Formula('~', Formula('&', left, right))
    if formula.root == '-|':  # NOR
        return Formula('~', Formula('|', left, right))
    raise ValueError(f"Unknown operator {formula.root}")

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        # Replace T with ~(p & ~p), F with (p & ~p)
        p = Formula(_DUMMY_VAR)
        if formula.root == 'T':
            return Formula('~', Formula('&', p, Formula('~', p)))
        else:  # 'F'
            return Formula('&', p, Formula('~', p))
    if is_unary(formula.root):
        return Formula('~', to_not_and(formula.first))
    left = to_not_and(formula.first)
    right = to_not_and(formula.second)
    if formula.root == '&':
        return Formula('&', left, right)
    if formula.root == '|':
        # p | q = ~(~p & ~q)
        return Formula('~',
                       Formula('&',
                               Formula('~', left),
                               Formula('~', right)))
    if formula.root == '->':
        # p -> q = ~(p & ~q)
        return Formula('~',
                       Formula('&', left, Formula('~', right)))
    if formula.root == '+':  # XOR
        # (p & ~q) | (~p & q) = ~(~(p & ~q) & ~(~p & q))
        term1 = Formula('&', left, Formula('~', right))
        term2 = Formula('&', Formula('~', left), right)
        return Formula('~',
                       Formula('&',
                               Formula('~', term1),
                               Formula('~', term2)))
    if formula.root == '<->':  # equivalence
        # (p & q) | (~p & ~q) = ~(~(p & q) & ~(~p & ~q))
        term1 = Formula('&', left, right)
        term2 = Formula('&', Formula('~', left), Formula('~', right))
        return Formula('~',
                       Formula('&',
                               Formula('~', term1),
                               Formula('~', term2)))
    if formula.root == '-&':  # NAND
        # p -& q = ~(p & q)
        return Formula('~', Formula('&', left, right))
    if formula.root == '-|':  # NOR
        # p -| q = ~p & ~q
        return Formula('&', Formula('~', left), Formula('~', right))
    raise ValueError(f"Unknown operator {formula.root}")

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        # Use dummy variable to generate constants
        p = Formula(_DUMMY_VAR)
        # T = (p -& (p -& p))
        # F = (T -& T)
        if formula.root == 'T':
            # p -& (p -& p) = ~(p & ~p) = T
            pp = Formula('-&', p, p)  # p -& p = ~p
            return Formula('-&', p, pp)
        else:  # 'F'
            # First get T
            t = to_nand(Formula('T'))  # recursive call, but careful: this will call again? We need to avoid infinite recursion.
            # Instead compute directly: T = (p -& (p -& p)), then F = T -& T
            pp = Formula('-&', p, p)
            t = Formula('-&', p, pp)
            return Formula('-&', t, t)
    if is_unary(formula.root):
        # ~f = f -& f
        f = to_nand(formula.first)
        return Formula('-&', f, f)
    left = to_nand(formula.first)
    right = to_nand(formula.second)
    if formula.root == '&':
        # p & q = (p -& q) -& (p -& q)
        pq = Formula('-&', left, right)
        return Formula('-&', pq, pq)
    if formula.root == '|':
        # p | q = (p -& p) -& (q -& q)
        pp = Formula('-&', left, left)
        qq = Formula('-&', right, right)
        return Formula('-&', pp, qq)
    if formula.root == '->':
        # p -> q = p -& (q -& q)
        qq = Formula('-&', right, right)
        return Formula('-&', left, qq)
    if formula.root == '+':  # XOR
        # p XOR q = (p & ~q) | (~p & q)
        # First compute ~p = p -& p, ~q = q -& q
        not_p = Formula('-&', left, left)
        not_q = Formula('-&', right, right)
        # p & ~q = ( (p -& not_q) -& (p -& not_q) )
        term1 = Formula('-&', left, not_q)
        term1 = Formula('-&', term1, term1)
        # ~p & q = ( (not_p -& q) -& (not_p -& q) )
        term2 = Formula('-&', not_p, right)
        term2 = Formula('-&', term2, term2)
        # OR of term1 and term2 = (term1 -& term1) -& (term2 -& term2)
        term1_not = Formula('-&', term1, term1)
        term2_not = Formula('-&', term2, term2)
        return Formula('-&', term1_not, term2_not)
    if formula.root == '<->':  # equivalence
        # p <-> q = (p & q) | (~p & ~q)
        # p & q = ( (left -& right) -& (left -& right) )
        pq = Formula('-&', left, right)
        pq = Formula('-&', pq, pq)
        # ~p & ~q = ( (not_p -& not_q) -& (not_p -& not_q) )
        not_p = Formula('-&', left, left)
        not_q = Formula('-&', right, right)
        pnq = Formula('-&', not_p, not_q)
        pnq = Formula('-&', pnq, pnq)
        # OR
        term1_not = Formula('-&', pq, pq)
        term2_not = Formula('-&', pnq, pnq)
        return Formula('-&', term1_not, term2_not)
    if formula.root == '-&':  # already NAND
        return Formula('-&', left, right)
    if formula.root == '-|':  # NOR
        # p -| q = ~(p | q) = (p | q) -& (p | q)
        # First compute p | q as above
        pp = Formula('-&', left, left)
        qq = Formula('-&', right, right)
        porq = Formula('-&', pp, qq)
        return Formula('-&', porq, porq)
    raise ValueError(f"Unknown operator {formula.root}")

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        p = Formula(_DUMMY_VAR)
        # T = p -> p, F = ~(p -> p)
        if formula.root == 'T':
            return Formula('->', p, p)
        else:  # 'F'
            return Formula('~', Formula('->', p, p))
    if is_unary(formula.root):
        return Formula('~', to_implies_not(formula.first))
    left = to_implies_not(formula.first)
    right = to_implies_not(formula.second)
    if formula.root == '->':
        return Formula('->', left, right)
    if formula.root == '&':
        # p & q = ~(p -> ~q)
        return Formula('~', Formula('->', left, Formula('~', right)))
    if formula.root == '|':
        # p | q = ~p -> q
        return Formula('->', Formula('~', left), right)
    if formula.root == '+':  # XOR
        # p XOR q = (p & ~q) | (~p & q)
        # p & ~q = ~(p -> q)
        term1 = Formula('~', Formula('->', left, right))
        # ~p & q = ~(~p -> ~q)? Actually ~p & q = ~(p -> q)? No. Use: ~p & q = ~(~p -> ~q)? Let's derive correctly:
        # ~p & q = ~(p | ~q) = ~( (~p) -> ~q )? Because p | ~q = ~p -> ~q. So ~(p | ~q) = ~( (~p) -> ~q ). But we can also use:
        # ~p & q = ~(p -> ~q)? Check: p -> ~q = ~p | ~q, so ~(p -> ~q) = p & q, not that.
        # Alternative: ~p & q = ~( (p) -> q )? p -> q = ~p | q, so ~(p -> q) = p & ~q, not.
        # Better: use the identity ~p & q = ~(p -> q) -> something? Let's use the standard transformation:
        # ~p & q = ~(~p -> ~q)? Because ~p -> ~q = p | ~q, so ~(~p -> ~q) = ~p & q. Yes.
        term2 = Formula('~', Formula('->', Formula('~', left), Formula('~', right)))
        # Now term1 | term2 = (~term1) -> term2
        return Formula('->', Formula('~', term1), term2)
    if formula.root == '<->':  # equivalence
        # p <-> q = (p & q) | (~p & ~q)
        # p & q = ~(p -> ~q)
        term1 = Formula('~', Formula('->', left, Formula('~', right)))
        # ~p & ~q = ~(~p -> q)
        term2 = Formula('~', Formula('->', Formula('~', left), right))
        return Formula('->', Formula('~', term1), term2)
    if formula.root == '-&':  # NAND
        # p -& q = ~(p & q) = p -> ~q
        return Formula('->', left, Formula('~', right))
    if formula.root == '-|':  # NOR
        # p -| q = ~(p | q) = ~(~p -> q)
        return Formula('~', Formula('->', Formula('~', left), right))
    raise ValueError(f"Unknown operator {formula.root}")

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    false = Formula('F')
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        if formula.root == 'T':
            # T = F -> F
            return Formula('->', false, false)
        else:  # 'F'
            return false
    if is_unary(formula.root):
        # ~p = p -> F
        return Formula('->', to_implies_false(formula.first), false)
    left = to_implies_false(formula.first)
    right = to_implies_false(formula.second)
    if formula.root == '->':
        return Formula('->', left, right)
    if formula.root == '&':
        # p & q = (p -> (q -> F)) -> F
        return Formula('->',
                       Formula('->', left, Formula('->', right, false)),
                       false)
    if formula.root == '|':
        # p | q = (p -> F) -> q
        return Formula('->', Formula('->', left, false), right)
    if formula.root == '+':  # XOR
        # p XOR q = (p & ~q) | (~p & q)
        # p & ~q = (p -> (q -> F)) -> F? Actually we derived p & ~q = (p -> q) -> F
        term1 = Formula('->', Formula('->', left, right), false)
        # ~p & q = (q -> p) -> F
        term2 = Formula('->', Formula('->', right, left), false)
        # term1 | term2 = (term1 -> F) -> term2
        return Formula('->', Formula('->', term1, false), term2)
    if formula.root == '<->':  # equivalence
        # p <-> q = (p -> q) & (q -> p)
        # (p -> q) & (q -> p) = ( (p->q) -> ( (q->p) -> F ) ) -> F
        impl1 = Formula('->', left, right)
        impl2 = Formula('->', right, left)
        return Formula('->',
                       Formula('->', impl1, Formula('->', impl2, false)),
                       false)
    if formula.root == '-&':  # NAND
        # p -& q = p -> (q -> F)
        return Formula('->', left, Formula('->', right, false))
    if formula.root == '-|':  # NOR
        # p -| q = (p -> F) & (q -> F) = ( (p->F) -> ( (q->F) -> F ) ) -> F
        not_p = Formula('->', left, false)
        not_q = Formula('->', right, false)
        return Formula('->',
                       Formula('->', not_p, Formula('->', not_q, false)),
                       false)
    raise ValueError(f"Unknown operator {formula.root}")
