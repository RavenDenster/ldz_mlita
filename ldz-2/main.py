import logging
import random
import copy
import time
import sys
from enum import Enum
from typing import List, Dict, Set, Optional, Union, Tuple, Any
from datetime import datetime

class Connective(Enum):
    OR = "∨"
    AND = "∧"
    IMPLIES = "→"

class Formula:
    def __init__(self, is_negative: bool = False):
        self.is_negative = is_negative
    
    def get_value(self) -> str:
        raise NotImplementedError
    
    def __eq__(self, other):
        if not isinstance(other, Formula):
            return False
        return str(self) == str(other)
    
    def __hash__(self):
        return hash(str(self))
    
    def __str__(self):
        raise NotImplementedError

class Variable(Formula):
    def __init__(self, value: str, is_negative: bool = False):
        super().__init__(is_negative)
        self.value = value
    
    def get_value(self) -> str:
        return f"¬{self.value}" if self.is_negative else self.value
    
    def neg_value(self) -> str:
        return f"¬{self.value}"
    
    def __str__(self):
        return f"¬{self.value}" if self.is_negative else self.value
    
    def copy(self):
        return Variable(self.value, self.is_negative)

class BinaryFormula(Formula):
    def __init__(self, left: Formula, connective: Connective, right: Formula, is_negative: bool = False):
        super().__init__(is_negative)
        self.left = left
        self.connective = connective
        self.right = right
    
    def get_value(self) -> str:
        return f"({self.left} {self.connective.value} {self.right})"
    
    def __str__(self):
        if self.is_negative:
            return f"¬({self.left} {self.connective.value} {self.right})"
        return f"({self.left} {self.connective.value} {self.right})"
    
    def copy(self):
        return BinaryFormula(self.left.copy(), self.connective, self.right.copy(), self.is_negative)

class Axiom:
    def __init__(self, name: str, formula: Formula):
        self.name = name
        self.formula = formula
    
    def __str__(self):
        return f"{self.name}: {self.formula}"

class FormulaCopier:
    @staticmethod
    def deep_copy(formula: Formula) -> Formula:
        if formula is None:
            return None
        
        if isinstance(formula, Variable):
            var = formula
            return Variable(var.value, var.is_negative)
        elif isinstance(formula, BinaryFormula):
            bin_formula = formula
            left_copy = FormulaCopier.deep_copy(bin_formula.left)
            right_copy = FormulaCopier.deep_copy(bin_formula.right)
            return BinaryFormula(left_copy, bin_formula.connective, right_copy, bin_formula.is_negative)
        
        raise ValueError(f"Unknown formula type: {type(formula)}")

class PatternFinder:
    def __init__(self, formula_copier: FormulaCopier):
        self.formula_copier = formula_copier
    
    def find_pattern_match(self, formula: Formula, pattern: Formula) -> Optional[Dict[str, Formula]]:
        current_substitution = {}
        if self._find_match(formula, pattern, current_substitution):
            return current_substitution
        return None
    
    def _find_match(self, formula: Formula, pattern: Formula, current_substitution: Dict[str, Formula]) -> bool:
        if isinstance(formula, BinaryFormula) and isinstance(pattern, BinaryFormula):
            bin_formula = formula
            bin_pattern = pattern
            
            if bin_pattern.connective != bin_formula.connective:
                return False
            
            return (self._find_match(bin_formula.left, bin_pattern.left, current_substitution) and
                    self._find_match(bin_formula.right, bin_pattern.right, current_substitution))
        elif isinstance(pattern, Variable):
            variable = pattern
            neg_formula = current_substitution.get(variable.neg_value())
            pos_formula = current_substitution.get(variable.value)
            
            if pos_formula is None and neg_formula is None:
                current_substitution[str(variable)] = self.formula_copier.deep_copy(formula)
                return True
            
            if pos_formula is not None:
                return pos_formula.get_value() == formula.get_value()
            
            return neg_formula.get_value() == formula.get_value()
        
        return False

class ImpliesConverter:
    @staticmethod
    def to_implies(formula: Formula) -> Formula:
        if isinstance(formula, BinaryFormula):
            bin_formula = formula
            left_conv = ImpliesConverter.to_implies(bin_formula.left)
            right_conv = ImpliesConverter.to_implies(bin_formula.right)
            
            if bin_formula.connective == Connective.OR:
                # A ∨ B ≡ ¬A → B
                left_conv.is_negative = not left_conv.is_negative
                or_impl = BinaryFormula(left_conv, Connective.IMPLIES, right_conv)
                or_impl.is_negative = bin_formula.is_negative
                return or_impl
            elif bin_formula.connective == Connective.AND:
                # A ∧ B ≡ ¬(A → ¬B)
                right_conv.is_negative = not right_conv.is_negative
                impl = BinaryFormula(left_conv, Connective.IMPLIES, right_conv)
                impl.is_negative = True
                if bin_formula.is_negative:
                    impl.is_negative = not impl.is_negative
                return impl
            elif bin_formula.connective == Connective.IMPLIES:
                return BinaryFormula(left_conv, Connective.IMPLIES, right_conv)
        
        if isinstance(formula, Variable):
            return Variable(formula.value, formula.is_negative)
        
        return formula

class CNFConverter:
    def __init__(self):
        pass
    
    def from_implies_to_clauses(self, formula: Formula) -> List[Formula]:
        without_impl = self._eliminate_implications(formula)
        nnf = self._to_nnf(without_impl)
        cnf = self._to_cnf(nnf)
        return self._split_into_clauses(cnf)
    
    def from_clauses_to_formula(self, clauses: List[Formula]) -> Formula:
        if not clauses:
            return None
        if len(clauses) == 1:
            return clauses[0]
        
        result = clauses[0]
        for i in range(1, len(clauses)):
            result = BinaryFormula(result, Connective.AND, clauses[i])
        return result
    
    def _eliminate_implications(self, formula: Formula) -> Formula:
        if isinstance(formula, Variable):
            return formula
        elif isinstance(formula, BinaryFormula):
            bin_formula = formula
            left = self._eliminate_implications(bin_formula.left)
            right = self._eliminate_implications(bin_formula.right)
            
            if bin_formula.connective == Connective.IMPLIES:
                # A → B ≡ ¬A ∨ B
                neg_left = self._negate(left)
                or_formula = BinaryFormula(neg_left, Connective.OR, right)
                or_formula.is_negative = False
                return or_formula
            else:
                return BinaryFormula(left, bin_formula.connective, right, bin_formula.is_negative)
        
        raise ValueError("Unknown formula type")
    
    def _to_nnf(self, formula: Formula) -> Formula:
        if isinstance(formula, Variable):
            return formula
        elif isinstance(formula, BinaryFormula):
            bin_formula = formula
            
            if bin_formula.is_negative:
                return self._apply_de_morgan(bin_formula)
            
            left = self._to_nnf(bin_formula.left)
            right = self._to_nnf(bin_formula.right)
            
            return BinaryFormula(left, bin_formula.connective, right, False)
        
        raise ValueError("Unknown formula type")
    
    def _apply_de_morgan(self, formula: BinaryFormula) -> Formula:
        left = formula.left
        right = formula.right
        connective = formula.connective
        
        if connective == Connective.IMPLIES:
            # ¬(¬A → B) ≡ ¬(A ∨ B) ≡ ¬A ∧ ¬B
            neg_left = self._negate(left)
            neg_right = self._negate(right)
            return BinaryFormula(neg_left, Connective.AND, neg_right, False)
        elif connective == Connective.AND:
            # ¬(A ∧ B) ≡ ¬A ∨ ¬B
            neg_left = self._negate(left)
            neg_right = self._negate(right)
            return BinaryFormula(neg_left, Connective.OR, neg_right, False)
        elif connective == Connective.OR:
            # ¬(A ∨ B) ≡ ¬A ∧ ¬B
            neg_left = self._negate(left)
            neg_right = self._negate(right)
            return BinaryFormula(neg_left, Connective.AND, neg_right, False)
        
        raise ValueError(f"Unsupported connective: {connective}")
    
    def _to_cnf(self, formula: Formula) -> Formula:
        if isinstance(formula, Variable):
            return formula
        elif isinstance(formula, BinaryFormula):
            bin_formula = formula
            left_cnf = self._to_cnf(bin_formula.left)
            right_cnf = self._to_cnf(bin_formula.right)
            
            if bin_formula.connective == Connective.AND:
                # A ∧ B уже в КНФ форме
                return BinaryFormula(left_cnf, Connective.AND, right_cnf)
            elif bin_formula.connective == Connective.OR:
                # (A ∨ B) нужно проверить дистрибутивность
                return self._distribute_or(left_cnf, right_cnf)
        
        raise ValueError("Formula should be in NNF")
    
    def _distribute_or(self, a: Formula, b: Formula) -> Formula:
        # Если A = C ∧ D
        if isinstance(a, BinaryFormula) and a.connective == Connective.AND:
            and_a = a
            # (C ∧ D) ∨ B ≡ (C ∨ B) ∧ (D ∨ B)
            left_or = self._distribute_or(and_a.left, b)
            right_or = self._distribute_or(and_a.right, b)
            return BinaryFormula(left_or, Connective.AND, right_or)
        # Если B = C ∧ D
        elif isinstance(b, BinaryFormula) and b.connective == Connective.AND:
            and_b = b
            # A ∨ (C ∧ D) ≡ (A ∨ C) ∧ (A ∨ D)
            left_or = self._distribute_or(a, and_b.left)
            right_or = self._distribute_or(a, and_b.right)
            return BinaryFormula(left_or, Connective.AND, right_or)
        # Ни A, ни B не являются AND
        else:
            return BinaryFormula(a, Connective.OR, b)
    
    def _split_into_clauses(self, formula: Formula) -> List[Formula]:
        clauses = set()
        
        if isinstance(formula, BinaryFormula):
            bin_formula = formula
            
            if bin_formula.connective == Connective.AND:
                clauses.update(self._split_into_clauses(bin_formula.left))
                clauses.update(self._split_into_clauses(bin_formula.right))
            else:
                clauses.add(formula)
        else:
            clauses.add(formula)
        
        return list(clauses)
    
    def _negate(self, formula: Formula) -> Formula:
        if isinstance(formula, Variable):
            var = formula
            return Variable(var.value, not var.is_negative)
        elif isinstance(formula, BinaryFormula):
            bin_formula = formula
            return BinaryFormula(bin_formula.left, bin_formula.connective, 
                               bin_formula.right, not bin_formula.is_negative)
        
        raise ValueError("Cannot negate formula")

class SubstitutionGenerator:
    @staticmethod
    def create_substitutions_for_axiom(formula: Formula, axiom: Axiom, num: int = None) -> List[Dict[str, Formula]]:
        axiom_variables = SubstitutionGenerator._exclude_variables(axiom.formula)
        all_parts = SubstitutionGenerator._exclude_parts(formula)
        all_parts.reverse()
        return SubstitutionGenerator._create_substitutions(all_parts, axiom_variables, num)
    
    @staticmethod
    def _create_substitutions(parts: List[Formula], variables: Set[str], num: int = None) -> List[Dict[str, Formula]]:
        substitutions = []
        vars_list = list(variables)
        
        generate_all = (num is None)
        if not vars_list or not parts or (not generate_all and num == 0):
            return substitutions
        
        current_indices = [0] * len(vars_list)
        
        while generate_all or len(substitutions) < num:
            substitution = {}
            for i in range(len(vars_list)):
                substitution[vars_list[i]] = parts[current_indices[i]]
            substitutions.append(substitution)

            carry = 1
            for i in range(len(vars_list) - 1, -1, -1):
                current_indices[i] += carry
                if current_indices[i] < len(parts):
                    carry = 0
                    break
                current_indices[i] = 0
                carry = 1
            
            if carry == 1:
                break
        
        return substitutions
    
    @staticmethod
    def _exclude_parts(formula: Formula) -> List[Formula]:
        stack = [formula]
        parts = []
        unique_parts = set()
        
        while stack:
            cur_formula = stack.pop(0)
            if cur_formula not in unique_parts:
                unique_parts.add(cur_formula)
                parts.append(cur_formula)
            
            if isinstance(cur_formula, BinaryFormula):
                stack.append(cur_formula.left)
                stack.append(cur_formula.right)
        
        return parts
    
    @staticmethod
    def _exclude_variables(formula: Formula) -> Set[str]:
        stack = [formula]
        variables = set()
        
        while stack:
            cur_formula = stack.pop()
            if isinstance(cur_formula, BinaryFormula):
                stack.append(cur_formula.left)
                stack.append(cur_formula.right)
            elif isinstance(cur_formula, Variable):
                variables.add(cur_formula.value)
        
        return variables

class AxiomSubstituter:
    def __init__(self, copier: FormulaCopier):
        self.copier = copier
    
    def apply_substitution(self, axiom: Axiom, substitution: Dict[str, Formula]) -> Formula:
        substitution_result = self._substitute_formula(axiom.formula, substitution)
        sub_str = {k: str(v) for k, v in substitution.items()}
        logging.debug(f"Подставляем в аксиому {axiom.formula} подстановку {sub_str}. Результат: {substitution_result}")
        return substitution_result
    
    def _substitute_formula(self, pattern: Formula, substitution: Dict[str, Formula]) -> Formula:
        if isinstance(pattern, BinaryFormula):
            bin_pattern = pattern
            return BinaryFormula(
                self._substitute_formula(bin_pattern.left, substitution),
                bin_pattern.connective,
                self._substitute_formula(bin_pattern.right, substitution)
            )
        elif isinstance(pattern, Variable):
            var_pattern = pattern
            return self.copier.deep_copy(substitution.get(var_pattern.value))
        
        raise RuntimeError("Impossible magic")

class ModusPonens:
    def __init__(self, pattern_finder: PatternFinder):
        self.pattern_finder = pattern_finder
        self.already_generated = set()
        self.pattern = BinaryFormula(Variable("A"), Connective.IMPLIES, Variable("B"))
    
    def find_modus_ponens(self, premises: List[Formula]) -> List[Formula]:
        new_formulas = []
        
        for i in range(len(premises)):
            A_implies_B = premises[i]
            result = self.pattern_finder.find_pattern_match(A_implies_B, self.pattern)
            
            if not result:
                continue
            
            if result.get("B") in self.already_generated:
                continue
            
            for j in range(len(premises)):
                if i != j:
                    A = premises[j]
                    
                    patterns = result
                    if patterns.get("A") == A:
                        B = patterns.get("B")
                        self.already_generated.add(B)
                        logging.debug(f"Найдено соответствие для MP. Посылка 1: {A}, Посылка с правилом вывода: {A_implies_B}, Новая посылка: {B}")
                        new_formulas.append(B)
        
        return new_formulas
    
    def add_already_generated(self, formula: Formula):
        self.already_generated.add(formula)
    
    def clear_cache(self):
        self.already_generated.clear()

class Deduction:
    def __init__(self, pattern_finder: PatternFinder, cnf_converter: CNFConverter, implies_converter: ImpliesConverter):
        self.pattern_finder = pattern_finder
        self.cnf_converter = cnf_converter
        self.implies_converter = implies_converter
        self.random = random.Random()
        self.pattern_cache = set()
        self.generated_results = set()
        self.pattern = BinaryFormula(Variable("A"), Connective.IMPLIES, Variable("B"))
    
    def random_deduct(self, premises: List[Formula]) -> List[Formula]:
        new_premises = []
        
        for premise in premises:
            if premise in self.pattern_cache:
                continue
            
            self.pattern_cache.add(premise)
            result = self.pattern_finder.find_pattern_match(premise, self.pattern)
            
            if result:
                patterns = result
                left = patterns.get("A")
                clauses = self.cnf_converter.from_implies_to_clauses(left)
                
                if not clauses:
                    continue
                
                random_clause_index = self.random.randint(0, len(clauses) - 1)
                chosen_formula = clauses[random_clause_index]
                clauses.pop(random_clause_index)
                
                right = patterns.get("B")
                new_right = BinaryFormula(chosen_formula, Connective.IMPLIES, right)
                
                if clauses:
                    new_left = self.implies_converter.to_implies(
                        self.cnf_converter.from_clauses_to_formula(clauses)
                    )
                    new_premise = BinaryFormula(new_left, Connective.IMPLIES, new_right)
                else:
                    new_premise = new_right
                
                if new_premise not in self.generated_results:
                    logging.debug(f"Применена теорема дедукции для посылки: {premise}, Новая посылка: {new_premise}")
                    new_premises.append(new_premise)
                    self.generated_results.add(new_premise)
        
        return new_premises
    
    def add_already_generated(self, formula: Formula):
        self.generated_results.add(formula)
    
    def clear_cache(self):
        self.pattern_cache.clear()
        self.generated_results.clear()

class SimpleAlgorithm:
    def __init__(self, deduction: Deduction, modus_ponens: ModusPonens, 
                 substitution_generator: SubstitutionGenerator, axiom_substituter: AxiomSubstituter,
                 implies_converter: ImpliesConverter):
        self.deduction = deduction
        self.modus_ponens = modus_ponens
        self.substitution_generator = substitution_generator
        self.axiom_substituter = axiom_substituter
        self.implies_converter = implies_converter
    
    def prove(self, formula: Formula, axioms: List[Axiom], log_to_file: bool = False, max_substitutions: int = 100) -> bool:
        self.modus_ponens.clear_cache()
        self.deduction.clear_cache()
        
        all_premises = set()

        formula = self.implies_converter.to_implies(formula)
        
        if log_to_file:
            logging.info(f"Преобразованная формула: {formula}")

        for axiom in axioms:
            subs = self.substitution_generator.create_substitutions_for_axiom(formula, axiom, max_substitutions)
            for sub in subs:
                all_premises.add(self.axiom_substituter.apply_substitution(axiom, sub))

        for premise in all_premises:
            self.modus_ponens.add_already_generated(premise)
            self.deduction.add_already_generated(premise)

        if self._find_formula(all_premises, formula, log_to_file):
            return True
        
        max_steps = 100
        for step in range(max_steps):
            current_list = list(all_premises)
            
            if log_to_file:
                logging.info("Используем правило вывода")
            else:
                print(f"{datetime.now().strftime('%H:%M:%S.%f')[:-3]}: Используем правило вывода")
            
            mp_results = self.modus_ponens.find_modus_ponens(current_list)
            if self._find_formula(mp_results, formula, log_to_file):
                return True
            
            all_premises.update(mp_results)
            
            if step % 3 == 0:
                if log_to_file:
                    logging.info("Используем теорему дедукции")
                else:
                    print(f"{datetime.now().strftime('%H:%M:%S.%f')[:-3]}: Используем теорему дедукции")
                
                deduction_results = self.deduction.random_deduct(current_list)
                if self._find_formula(deduction_results, formula, log_to_file):
                    return True
                
                all_premises.update(deduction_results)
            
            if log_to_file:
                logging.info(f"Step {step}: {len(all_premises)} formulas")
            else:
                print(f"{datetime.now().strftime('%H:%M:%S.%f')[:-3]}: Step {step}: {len(all_premises)} formulas")
            
            if len(all_premises) > 10000:
                if log_to_file:
                    logging.warning("Too many formulas, stopping")
                else:
                    print(f"{datetime.now().strftime('%H:%M:%S.%f')[:-3]}: Too many formulas, stopping")
                break
        
        if log_to_file:
            logging.warning(f"Failed to prove {formula}")
        else:
            print(f"{datetime.now().strftime('%H:%M:%S.%f')[:-3]}: Failed to prove {formula}")
        return False
    
    def _find_formula(self, premises, formula: Formula, log_to_file: bool) -> bool:
        if formula in premises:
            if log_to_file:
                logging.info("===================Алгоритм доказал формулу=====================")
                logging.info(f"Формула была выведена: {formula}")
            else:
                print(f"{datetime.now().strftime('%H:%M:%S.%f')[:-3]}: ===================Алгоритм доказал формулу=====================")
                print(f"{datetime.now().strftime('%H:%M:%S.%f')[:-3]}: Формула была выведена: {formula}")
            return True
        return False

class AxiomBuilder:
    @staticmethod
    def build_axioms_A1_A3() -> List[Axiom]:
        axioms = []
        
        A = Variable("A")
        B = Variable("B")
        C = Variable("C")
        
        notA = Variable("A", True)
        notB = Variable("B", True)
        
        # A1: (A→(B→A))
        A1_formula = BinaryFormula(A, Connective.IMPLIES, 
                                 BinaryFormula(B, Connective.IMPLIES, A))
        axioms.append(Axiom("A1", A1_formula))
        
        # A2: ((A→(B→C))→((A→B)→(A→C)))
        A2_formula = BinaryFormula(
            BinaryFormula(A, Connective.IMPLIES, 
                         BinaryFormula(B, Connective.IMPLIES, C)),
            Connective.IMPLIES,
            BinaryFormula(
                BinaryFormula(A, Connective.IMPLIES, B),
                Connective.IMPLIES,
                BinaryFormula(A, Connective.IMPLIES, C)
            )
        )
        axioms.append(Axiom("A2", A2_formula))
        
        # A3: ((¬B→¬A)→((¬B→A)→B))
        notB_implies_notA = BinaryFormula(notB, Connective.IMPLIES, notA)
        notB_implies_A = BinaryFormula(notB, Connective.IMPLIES, A)
        notB_implies_A_implies_B = BinaryFormula(notB_implies_A, Connective.IMPLIES, B)
        A3_formula = BinaryFormula(notB_implies_notA, Connective.IMPLIES, notB_implies_A_implies_B)
        axioms.append(Axiom("A3", A3_formula))
        
        return axioms
    
    @staticmethod
    def build_axioms_A4_A11() -> List[Axiom]:
        axioms = []
        
        A = Variable("A")
        B = Variable("B")
        C = Variable("C")
        notA = Variable("A", True)
        
        # A4: A∧B→A
        A4_formula = BinaryFormula(
            BinaryFormula(A, Connective.AND, B),
            Connective.IMPLIES,
            A
        )
        axioms.append(Axiom("A4", A4_formula))
        
        # A5: A∧B→B
        A5_formula = BinaryFormula(
            BinaryFormula(A, Connective.AND, B),
            Connective.IMPLIES,
            B
        )
        axioms.append(Axiom("A5", A5_formula))
        
        # A6: A→(B→(A∧B))
        A6_formula = BinaryFormula(
            A,
            Connective.IMPLIES,
            BinaryFormula(
                B,
                Connective.IMPLIES,
                BinaryFormula(A, Connective.AND, B)
            )
        )
        axioms.append(Axiom("A6", A6_formula))
        
        # A7: A→(A∨B)
        A7_formula = BinaryFormula(
            A,
            Connective.IMPLIES,
            BinaryFormula(A, Connective.OR, B)
        )
        axioms.append(Axiom("A7", A7_formula))
        
        # A8: B→(A∨B)
        A8_formula = BinaryFormula(
            B,
            Connective.IMPLIES,
            BinaryFormula(A, Connective.OR, B)
        )
        axioms.append(Axiom("A8", A8_formula))
        
        # A9: (A→C)→((B→C)→((A∨B)→C))
        A_implies_C = BinaryFormula(A, Connective.IMPLIES, C)
        B_implies_C = BinaryFormula(B, Connective.IMPLIES, C)
        A_or_B = BinaryFormula(A, Connective.OR, B)
        A_or_B_implies_C = BinaryFormula(A_or_B, Connective.IMPLIES, C)
        B_implies_C_implies_A_or_B_implies_C = BinaryFormula(B_implies_C, Connective.IMPLIES, A_or_B_implies_C)
        A9_formula = BinaryFormula(A_implies_C, Connective.IMPLIES, B_implies_C_implies_A_or_B_implies_C)
        axioms.append(Axiom("A9", A9_formula))
        
        # A10: ¬A→(A→B)
        A10_formula = BinaryFormula(
            notA,
            Connective.IMPLIES,
            BinaryFormula(A, Connective.IMPLIES, B)
        )
        axioms.append(Axiom("A10", A10_formula))
        
        # A11: A∨¬A
        A11_formula = BinaryFormula(A, Connective.OR, notA)
        axioms.append(Axiom("A11", A11_formula))
        
        return axioms

def create_components():
    formula_copier = FormulaCopier()
    pattern_finder = PatternFinder(formula_copier)
    cnf_converter = CNFConverter()
    implies_converter = ImpliesConverter()
    substitution_generator = SubstitutionGenerator()
    axiom_substituter = AxiomSubstituter(formula_copier)
    modus_ponens = ModusPonens(pattern_finder)
    deduction = Deduction(pattern_finder, cnf_converter, implies_converter)
    algorithm = SimpleAlgorithm(deduction, modus_ponens, substitution_generator, 
                               axiom_substituter, implies_converter)
    
    return algorithm

def setup_file_logging(filename: str):
    """Настройка логирования в файл"""
    logger = logging.getLogger()
    logger.setLevel(logging.DEBUG)

    for handler in logger.handlers[:]:
        logger.removeHandler(handler)

    file_handler = logging.FileHandler(filename, mode='w', encoding='utf-8')
    file_handler.setLevel(logging.DEBUG)

    formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    file_handler.setFormatter(formatter)
    
    logger.addHandler(file_handler)
    
    return logger

def setup_console_logging():
    """Настройка логирования в консоль только для INFO и выше (без DEBUG)"""
    logger = logging.getLogger()

    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setLevel(logging.INFO)

    formatter = logging.Formatter('%(message)s')
    console_handler.setFormatter(formatter)

    for handler in logger.handlers[:]:
        logger.removeHandler(handler)
    logger.addHandler(console_handler)
    logger.setLevel(logging.INFO)

def test_all_axioms(verbose: bool = True):
    algorithm = create_components()
    axioms_A1_A3 = AxiomBuilder.build_axioms_A1_A3()
    axioms_to_prove = AxiomBuilder.build_axioms_A4_A11()
    
    total_time = 0
    results = []
    
    for i, axiom in enumerate(axioms_to_prove, 4):
        axiom_name = axiom.name[1:]
        
        print(f"\nДоказываем аксиому A{axiom_name}: {axiom.formula}")
        
        if verbose:
            log_filename = f"A{axiom_name}.log"
            print(f"Подробный лог записывается в файл: {log_filename}")
            print("=" * 60)

            setup_file_logging(log_filename)

            logging.info(f"============Начало доказательства==============")

            start_time = time.time()
            success = algorithm.prove(axiom.formula, axioms_A1_A3, log_to_file=True, max_substitutions=100)
            end_time = time.time()

            for handler in logging.getLogger().handlers[:]:
                if isinstance(handler, logging.FileHandler):
                    handler.close()
                    logging.getLogger().removeHandler(handler)
            
        else:

            print("=" * 60)

            setup_console_logging()
            
            start_time = time.time()
            success = algorithm.prove(axiom.formula, axioms_A1_A3, log_to_file=False, max_substitutions=100)
            end_time = time.time()
        
        elapsed = end_time - start_time
        total_time += elapsed

        results.append({
            'axiom': f"A{axiom_name}",
            'success': success,
            'time': elapsed
        })
        
        if not verbose:
            if success:
                print(f"Доказана за {elapsed:.3f} секунд")
            else:
                print(f"Не удалось доказать")

    print("\n" + "="*60)
    print("ИТОГИ ДОКАЗАТЕЛЬСТВА:")
    print("="*60)
    
    for result in results:
        status = "Доказана" if result['success'] else "Не доказана"
        print(f"{result['axiom']}: {status} ({result['time']:.3f} сек)")
    
    print(f"\nОбщее время: {total_time:.3f} секунд")

def main():
    print("Выберите режим вывода:")
    print("1. Подробный (со всеми шагами и подстановками в файлы .log)")
    print("2. Краткий (только основные шаги в терминале)")
    
    choice = input("Введите 1 или 2: ").strip()
    
    if choice == "1":
        print("\n" + "="*60)
        print("ПОДРОБНЫЙ РЕЖИМ ВЫВОДА")
        print("Логи будут записаны в файлы A4.log, A5.log и т.д.")
        print("="*60)
        test_all_axioms(verbose=True)
    elif choice == "2":
        print("\n" + "="*60)
        print("КРАТКИЙ РЕЖИМ ВЫВОДА")
        print("="*60)
        test_all_axioms(verbose=False)
    else:
        print("Неверный выбор. Используется краткий режим.")
        test_all_axioms(verbose=False)

if __name__ == "__main__":
    main()