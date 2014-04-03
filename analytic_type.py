r"""
Functor construction for all spaces (artificial to make the coercion framework work)

AUTHORS:

- Jonas Jermann (2013): initial version

"""

#*****************************************************************************
#       Copyright (C) 2013 Jonas Jermann <jjermann2@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.sets.set import Set
from sage.combinat.posets.posets import Poset, FinitePoset
from sage.combinat.posets.lattices import FiniteLatticePoset
from sage.combinat.posets.elements import LatticePosetElement


class AnalyticTypeElement(LatticePosetElement):
    r"""
    Analytic types of forms and/or spaces
    
    The class derives from LatticePosetElement.
    An analytic type element describes what basic analytic
    properties are contained/included in ``self``.
    """

    # We use the same constructor as LatticePosetElement
    #def __init__(self, poset, element, vertex):
    #    super(AnalyticTypeElement, self).__init__(poset, element, vertex)

    def _repr_(self):
        r"""
        Return the string representation of ``self``.
        """

        return self.analytic_name()

    def _latex_(self):
        r"""
        Return the LaTeX representation of ``self``.
        """

        from sage.misc.latex import latex
        return latex(self.analytic_name())

    def analytic_space_name(self):
        r"""
        Return the (analytic part of the) name of a space
        with the analytic type of ``self``.

        This is used for the string representation of such spaces.
        """

        name = ""
        if   self.parent()("quasi") <= self:
             name += "Quasi"
        if   self.parent()("mero")  <= self:
             name += "MeromorphicModular"
        elif self.parent()("weak")  <= self:
             name += "WeakModular"
        elif self.parent()("holo")  <= self:
             name += "Modular"
        elif self.parent()("cusp")  <= self:
             name += "Cusp"
        else:
             name  = "Zero"

        return name

    def latex_space_name(self):
        r"""
        Return the short (analytic part of the) name of a space
        with the analytic type of ``self`` for usage with latex.

        This is used for the latex representation of such spaces.
        """

        name = ""
        if   self.parent()("quasi") <= self:
             name += "Q"
        if   self.parent()("mero")  <= self:
             name += "\\tilde{M}"
        elif self.parent()("weak")  <= self:
             name += "M^!"
        elif self.parent()("holo")  <= self:
             name += "M"
        elif self.parent()("cusp")  <= self:
             name += "C"
        else:
             name  = "Z"

        return name

    def analytic_name(self):
        r"""
        Return a string representation of the analytic type.
        """

        name = ""
        if   self.parent()("quasi") <= self:
             name += "quasi "
        if   self.parent()("mero")  <= self:
             name += "meromorphic modular"
        elif self.parent()("weak")  <= self:
             name += "weakly holomorphic modular"
        elif self.parent()("holo")  <= self:
             name += "modular"
        elif self.parent()("cusp")  <= self:
             name += "cuspidal"
        else:
             name  = "zero"

        return name

    def reduce_to(self, reduce_type):
        r"""
        Return a new analytic type which contains only analytic properties
        specified in both ``self`` and ``reduce_type``.

        INPUT:

        - ``reduce_type``   - An analytic type or something which is
                              convertable to an analytic type.

        OUTPUT:

        The new reduced analytic type.
        """

        reduce_type = self.parent()(reduce_type)
        return self * reduce_type

    def extend_by(self, extend_type):
        r"""
        Return a new analytic type which contains all analytic properties
        specified either in ``self`` or in ``extend_type``.

        INPUT:

        - ``extend_type``   - An analytic type or something which is
                              convertable to an analytic type.

        OUTPUT:

        The new extended analytic type.
        """

        extend_type = self.parent()(extend_type)
        return self + extend_type

    # is it ok to define the iterator that way (strings on el.element for el in self.element)??
    # alternatively: go through all x with x<=y of of the analytic type element y
    # or return the Poset Element instead of the string
    def __iter__(self):
        r"""
        Return an iterator of ``self`` which gives the basic analytic
        properties contained in ``self`` as strings.
        """

        return iter([el.element for el in self.element])
    

class AnalyticType(FiniteLatticePoset):
    r"""
    Container for all possible analytic types of forms and/or spaces
    """

    Element = AnalyticTypeElement

    @staticmethod
    def __classcall__(cls):
        r"""
        Directly return the classcall of UniqueRepresentation
        (skipping the classcalls of the other superclasses).

        That's because ``self`` is supposed to be used as a Singleton.
        It initializes the FinitelatticePoset with the proper arguments
        by itself in ``self.__init__()``.
        """

        return super(FinitePoset, cls).__classcall__(cls)
                
    def __init__(self):
        r"""
        Container for all possible analytic types of forms and/or spaces.

        This class is supposed to be used as a Singleton.

        It first creates a ``Poset`` that contains all basic analytic
        properties to be modeled by the AnalyticType. Then the order
        ideals lattice of that Poset is taken as the underlying
        FiniteLatticePoset of ``self``.

        In particular elements of ``self`` describe what basic analytic
        properties are contained/included in that element.
        """

        # We (arbitrarily) choose to model by inclusion instead of restriction
        P_elements = [ "cusp", "holo", "weak", "mero", "quasi"]
        P_relations = [["cusp", "holo"], ["holo", "weak"], ["weak", "mero"]]
        
        self._base_poset = Poset([P_elements, P_relations], cover_relations=True, facade=False)
        L = self._base_poset.order_ideals_lattice()
        L = FiniteLatticePoset(L, facade=False)

        FiniteLatticePoset.__init__(self, hasse_diagram=L._hasse_diagram, elements=L._elements, category=L.category(), facade=L._is_facade, key=None)

    def _repr_(self):
        r"""
        Return the string representation of ``self``.
        """

        return "Analytic Type"

    def __call__(self, *args, **kwargs):
        r"""
        Return the result of the corresponding call function
        of ``FiniteLatticePoset``.

        If more than one argument is given it is called with
        the list of those arguments instead.
        """

        if len(args)>1:
            return super(AnalyticType,self).__call__([arg for arg in args], **kwargs)
        else:
            return super(AnalyticType,self).__call__(*args, **kwargs)

    def _element_constructor_(self, element):
        r"""
        Return ``element`` coerced into an element of ``self``.

        INPUT:

        - ``element``   - Either something which coerces in the
                          ``FiniteLatticePoset`` of ``self`` or
                          a string or a list of strings of basic
                          properties that should be contained in
                          the new element.
                          

        OUTPUT:

        An element of ``self`` corresponding to ``element``
        (resp. containing all specified basic analytic properties).
        """
        
        if type(element)==str:
            element=[element]
        if isinstance(element,list) or isinstance(element,tuple):
            element = Set(self._base_poset.order_ideal([self._base_poset(s) for s in element]))

        return super(AnalyticType, self)._element_constructor_(element)

        #res = self.first()
        #for element in args:
        #    if type(element)==str:
        #        element=[element]
        #    if isinstance(element,list) or isinstance(element,tuple):
        #        element = Set(self._base_poset.order_ideal([self._base_poset(s) for s in element]))
        #    element = super(AnalyticType,self)._element_constructor_(element)
        #    res += element
        #return res
