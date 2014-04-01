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
    def __init__(self, poset, element, vertex):
        super(AnalyticTypeElement, self).__init__(poset, element, vertex)

    def _repr_(self):
        return self.analytic_name()

    def _latex_(self):
        r"""
        Return the LaTeX representation of ``self``.
        """
        from sage.misc.latex import latex
        return latex(self.analytic_name())

    def analytic_space_name(self):
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
        elif self.parent()("mcusp") <= self:
             name += "MCusp"
        else:
             name  = "Zero"

        return name

    def latex_space_name(self):
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
        elif self.parent()("mcusp") <= self:
             name += "MC"
        else:
             name  = "Z"

        return name

    def analytic_name(self):
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
        elif self.parent()("mcusp") <= self:
             name += "(modular) cuspidal"
        else:
             name  = "zero"

        return name

    def reduce_to(self, reduce_type):
        reduce_type = self.parent()(reduce_type)
        return self * reduce_type

    def extend_by(self, extend_type):
        extend_type = self.parent()(extend_type)
        return self + extend_type

    # is it ok to define the iterator that way (strings on el.element for el in self.element)??
    # alternatively: go through all x with x<=y of of the analytic type element y
    # or return the Poset Element instead of the string
    def __iter__(self):
        return iter([el.element for el in self.element])
    

class AnalyticType(FiniteLatticePoset):
    Element = AnalyticTypeElement

    @staticmethod
    def __classcall__(cls, *args, **options):
        return super(FinitePoset, cls).__classcall__(cls, *args, **options)
                
    def __init__(self, *args, **options):
        # We (arbitrarily) choose to model by inclusion instead of restriction
        P_elements = [ "mcusp", "cusp", "holo", "weak", "mero", "quasi"]
        P_relations = [["mcusp", "cusp"], ["cusp", "holo"], ["holo", "weak"], ["weak", "mero"]]
        
        self._base_poset = Poset([P_elements, P_relations], cover_relations=True, facade=False)
        L = self._base_poset.order_ideals_lattice()
        L = FiniteLatticePoset(L, facade=False)

        FiniteLatticePoset.__init__(self, hasse_diagram=L._hasse_diagram, elements=L._elements, category=L.category(), facade=L._is_facade, key=None)

    def _repr_(self):
        return "Analytic Type"

    def __call__(self, *args, **kwargs):
        if len(args)>1:
            return super(AnalyticType,self).__call__([arg for arg in args], **kwargs)
        else:
            return super(AnalyticType,self).__call__(*args, **kwargs)

    def _element_constructor_(self, element):
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
