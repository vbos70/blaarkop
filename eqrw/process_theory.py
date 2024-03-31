from utils import *
from itertools import chain

class Theory(AttrDict):
    """Theories represent equational theories with Python dictionaries. 
    Theories have variables, atoms, and axioms."""


    def __init__(self, **kws):
        ''' Create a Theory with the given variables, atoms, and axioms.

        If `kws["variables"]` exists, it shall be a lis of `process.Var` objects 
        representing the theory's variables. Otherwise, the theory has no variables. 

        If `kws["atoms"]` exists, it shall be a list of `process.Atom` objects
        representing the theory's atoms. Otherwise, the theory has no atoms.

        Any other element `kws["ax"]` shall be a `process.Equality` object
        representing an process equality axioms with name "ax".

        `Theory` objects are `AttrDict` objetcs and as such allow attribute acess 
        notation to look up values. If `t : Theory`, then

            t.ax == t['ax']  # provided that ax is not a real attribute/method of Theory. 
        '''
        self._variables = None
        if 'variables' in kws:
            self._variables = kws['variables']
            del kws['variables']
        
        self._atoms = None
        if 'atoms' in kws:
            self._atoms = kws['atoms']
            del kws['atoms']
                
        super().__init__(**kws)


    def variables(self):
        '''Returns a list of all variables in this `Theory`.'''
        if self._variables is None:
            vs = []
            for eq in self.values():
                for v in chain(eq.lhs.vars(), eq.rhs.vars()):
                    if v not in vs:
                        vs.append(v)
            self._variables = vs
        return self._variables

    def var_names(self):
        '''compute list of process variables names'''
        return [v.name for v in self.variables()]


    def atoms(self):
        '''Returns a list of all atoms in this `Theory`.'''
        if self._atoms is None:
            ats = []
            for eq in self.values():
                for a in chain(eq.lhs.atoms(), eq.rhs.atoms()):
                    if a not in ats:
                        ats.append(a)
            self._atoms = ats
        return self._atoms


    def atom_names(self):
        '''compute list of process atoms names'''
        return [a.name for a in self.atoms()]

    def __str__(self):
        result = []
        vs = self.var_names()
        if len(vs)>0:
            result.append(f"# Variables\n{', '.join(vs)}")
        ats = self.atom_names()
        if len(ats)>0:
            result.append(f"# Atoms\n{', '.join(ats)}")
        result.append("# Axioms")
        result.extend(f'{ax}: {self[ax]}' for ax in self)
 
        return "\n".join(result)
        