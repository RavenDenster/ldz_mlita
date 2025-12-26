"""
SAT Solver на основе алгоритма DPLL.
Поддерживает формат входных файлов DIMACS CNF.
"""

import sys
import time
from typing import List, Set, Tuple, Optional, Dict

class SATSolver:
    """Класс SAT-решателя, реализующего алгоритм DPLL."""
    
    def __init__(self):
        self.variables = set()
        self.clauses = []
        self.assignment = {}
        self.stats = {
            'decisions': 0,
            'unit_propagations': 0,
            'pure_eliminations': 0,
            'backtracks': 0
        }
    
    def parse_dimacs(self, filename: str) -> None:
        """
        Парсит файл в формате DIMACS CNF.
        
        Исправленная версия: корректно обрабатывает файлы с лишними символами.
        """
        try:
            with open(filename, 'r') as f:
                lines = f.readlines()
        except FileNotFoundError:
            print(f"Ошибка: Файл '{filename}' не найден.")
            sys.exit(1)
        except Exception as e:
            print(f"Ошибка при чтении файла: {e}")
            sys.exit(1)
        
        for line in lines:
            line = line.strip()

            if not line or line.startswith('c'):
                continue
 
            if line.startswith('p'):
                parts = line.split()
                if len(parts) != 4 or parts[1] != 'cnf':
                    print("Ошибка: Неверный формат заголовка в файле CNF.")
                    sys.exit(1)
                num_vars = int(parts[2])
                num_clauses = int(parts[3])
                self.variables = set(range(1, num_vars + 1))
                continue

            parts = line.split()
            if not parts:
                continue

            literals = []
            for part in parts:
                if part == '%':
                    continue
                try:
                    num = int(part)
                    if num == 0:
                        break  
                    literals.append(num)
                except ValueError:
                    continue
            
            if literals:
                self.clauses.append(literals)

        print(f"Прочитано {len(self.clauses)} дизъюнктов")
        print(f"Переменные: от 1 до {len(self.variables)}")
        
    def simplify(self, clauses: List[List[int]], assignment: Dict[int, bool]) -> Tuple[List[List[int]], Dict[int, bool], bool]:
        """
        Упрощает формулу, применяя правила единичного дизъюнкта и чистого литерала.
        
        Возвращает:
        - Упрощенные дизъюнкты
        - Обновленное присваивание
        - Флаг противоречия (True если найдено противоречие)
        """
        changed = True
        contradiction = False
        
        while changed and not contradiction:
            changed = False

            unit_clauses = [c for c in clauses if len(c) == 1]
            for unit in unit_clauses:
                lit = unit[0]
                var = abs(lit)
                value = lit > 0

                if var in assignment and assignment[var] != value:
                    contradiction = True
                    break
                
                if var not in assignment:
                    assignment[var] = value
                    self.stats['unit_propagations'] += 1
                    changed = True
            
            if contradiction:
                break

            new_clauses = []
            for clause in clauses:

                satisfied = False
                new_literals = []
                
                for lit in clause:
                    var = abs(lit)
                    if var in assignment:
                        if (lit > 0 and assignment[var]) or (lit < 0 and not assignment[var]):
                            satisfied = True
                            break

                    else:
                        new_literals.append(lit)
                
                if not satisfied:
                    if not new_literals:
                        contradiction = True
                        break
                    new_clauses.append(new_literals)
            
            if contradiction:
                break
            
            clauses = new_clauses

            literal_count = {}
            for clause in clauses:
                for lit in clause:
                    literal_count[lit] = literal_count.get(lit, 0) + 1
            
            pure_literals = []
            for lit in literal_count:
                var = abs(lit)
                if -lit not in literal_count:
                    if var not in assignment:
                        pure_literals.append(lit)
            
            for lit in pure_literals:
                var = abs(lit)
                value = lit > 0
                assignment[var] = value
                self.stats['pure_eliminations'] += 1
                changed = True
        
        return clauses, assignment, contradiction
    
    def choose_variable(self, clauses: List[List[int]], assignment: Dict[int, bool]) -> Optional[int]:
        """Выбирает переменную для решения (эвристика: наиболее часто встречающаяся)."""
        unassigned_vars = [v for v in self.variables if v not in assignment]
        if not unassigned_vars:
            return None
        
        # Эвристика: выбираем переменную, которая встречается в наибольшем числе дизъюнктов
        var_count = {}
        for clause in clauses:
            for lit in clause:
                var = abs(lit)
                if var in unassigned_vars:
                    var_count[var] = var_count.get(var, 0) + 1
        
        if var_count:
            return max(var_count.items(), key=lambda x: x[1])[0]
        else:
            return unassigned_vars[0]
    
    def dpll(self, clauses: List[List[int]], assignment: Dict[int, bool]) -> Optional[Dict[int, bool]]:
        """
        Рекурсивная реализация алгоритма DPLL.
        
        Возвращает:
        - Присваивание, если формула выполнима
        - None, если формула невыполнима
        """
        clauses, assignment, contradiction = self.simplify(clauses, assignment)
        
        if contradiction:
            self.stats['backtracks'] += 1
            return None
  
        if not clauses:
            return assignment
  
        var = self.choose_variable(clauses, assignment)
        if var is None:
            return assignment
        
        self.stats['decisions'] += 1
  
        new_assignment = assignment.copy()
        new_assignment[var] = True
        result = self.dpll(clauses, new_assignment)
        
        if result is not None:
            return result

        new_assignment = assignment.copy()
        new_assignment[var] = False
        result = self.dpll(clauses, new_assignment)
        
        if result is not None:
            return result
        
        self.stats['backtracks'] += 1
        return None
    
    def solve(self) -> Tuple[bool, Optional[Dict[int, bool]]]:
        """Основной метод для решения SAT проблемы."""
        start_time = time.time()

        result = self.dpll(self.clauses.copy(), {})
        
        elapsed_time = time.time() - start_time
        
        if result is not None:
            for var in self.variables:
                if var not in result:
                    result[var] = True 
            
            print(f"Результат: ВЫПОЛНИМА")
            print(f"Время выполнения: {elapsed_time:.4f} секунд")
            print(f"Статистика:")
            print(f"  Решений: {self.stats['decisions']}")
            print(f"  Единичных дизъюнктов: {self.stats['unit_propagations']}")
            print(f"  Чистых литералов: {self.stats['pure_eliminations']}")
            print(f"  Возвратов: {self.stats['backtracks']}")
            return True, result
        else:
            print(f"Результат: НЕВЫПОЛНИМА")
            print(f"Время выполнения: {elapsed_time:.4f} секунд")
            return False, None
    
    def print_solution(self, assignment: Dict[int, bool]) -> None:
        """Выводит решение в читаемом формате."""
        if assignment is None:
            return
        
        print("\n" + "="*50)
        print("НАЙДЕННОЕ РЕШЕНИЕ:")
        print("="*50)

        sorted_vars = sorted(assignment.keys())

        for var in sorted_vars:
            value = "ИСТИНА" if assignment[var] else "ЛОЖЬ"
            print(f"x{var} = {value}")

        print("\nКомпактное представление (1=ИСТИНА, 0=ЛОЖЬ):")
        true_vars = [var for var in sorted_vars if assignment[var]]
        false_vars = [var for var in sorted_vars if not assignment[var]]
        
        print(f"Истинные переменные: {true_vars}")
        print(f"Ложные переменные: {false_vars}")

        if self.verify_solution(assignment):
            print("\nРешение верифицировано: все дизъюнкты удовлетворены")
        else:
            print("\nОшибка: решение не удовлетворяет всем дизъюнктам")
    
    def verify_solution(self, assignment: Dict[int, bool]) -> bool:
        """Проверяет, удовлетворяет ли присваивание всем дизъюнктам."""
        for clause in self.clauses:
            clause_satisfied = False
            for lit in clause:
                var = abs(lit)
                if var in assignment:
                    if (lit > 0 and assignment[var]) or (lit < 0 and not assignment[var]):
                        clause_satisfied = True
                        break
            if not clause_satisfied:
                return False
        return True


def main():
    """Основная функция для запуска из командной строки."""
    print("="*60)
    print("SAT-РЕШАТЕЛЬ НА ОСНОВЕ АЛГОРИТМА DPLL")
    print("="*60)
    
    if len(sys.argv) != 2:
        print("Использование: python sat_solver.py <файл.cnf>")
        print("\nПримеры:")
        print("  python sat_solver.py uf20-01.cnf")
        print("  python sat_solver.py пример.cnf")
        sys.exit(1)
    
    filename = sys.argv[1]

    solver = SATSolver()
    
    print(f"Чтение файла: {filename}")
    solver.parse_dimacs(filename)
    
    print(f"Задача: {len(solver.variables)} переменных, {len(solver.clauses)} дизъюнктов")
    
    print("\nРешение...")
    satisfiable, solution = solver.solve()
    
    if satisfiable and solution:
        solver.print_solution(solution)
    
    print("\n" + "="*60)


if __name__ == "__main__":
    main()