import sys
from enum import Enum

class Parser:
    def __init__(self, exp: str):
        self.exp = exp
        self.pos = 0
        self.length = len(exp)
        self.ch = None 
        self.read_ch()

    def read_ch(self) -> None:
        """Читает следующий символ или устанавливает None в конце строки"""
        if self.pos < self.length:
            self.ch = self.exp[self.pos]
            self.pos += 1
        else:
            self.ch = None

    def match(self, expected: str) -> bool:
        """Проверяет соответствие текущего символа ожидаемому"""
        if self.ch == expected:
            self.read_ch()
            return True
        return False

    # ========== Методы для нетерминалов ==========
    
    def expr(self) -> bool:
        """<expr> ::= <bracket_seq> | ε"""
        if self.ch == '(' or self.ch == '[':
            return self.bracket_seq()
        # ε-правило - пустая строка допустима
        return True

    def bracket_seq(self) -> bool:
        """<bracket_seq> ::= '(' <round_part> ')' <tail1> | '[' <square_part> ']' <tail2>"""
        if self.ch == '(':
            return self._parse_round_seq()
        elif self.ch == '[':
            return self._parse_square_seq()
        return False

    def _parse_round_seq(self) -> bool:
        """Обрабатывает '(' <round_part> ')' <tail1>"""
        if not self.match('('):
            return False
        if not self.round_part():
            return False
        if not self.match(')'):
            return False
        return self.tail1()

    def _parse_square_seq(self) -> bool:
        """Обрабатывает '[' <square_part> ']' <tail2>"""
        if not self.match('['):
            return False
        if not self.square_part():
            return False
        if not self.match(']'):
            return False
        return self.tail2()

    def round_part(self) -> bool:
        """<round_part> ::= <bracket_seq> | ε"""
        if self.ch == '(' or self.ch == '[':
            return self.bracket_seq()
        # ε-правило
        return True

    def square_part(self) -> bool:
        """<square_part> ::= <bracket_seq> | ε"""
        if self.ch == '(' or self.ch == '[':
            return self.bracket_seq()
        # ε-правило
        return True

    def tail1(self) -> bool:
        """<tail1> ::= '[' <square_part> ']' <tail2> | ε"""
        if self.ch == '[':
            if not self.match('['):
                return False
            if not self.square_part():
                return False
            if not self.match(']'):
                return False
            return self.tail2()
        # ε-правило
        return True

    def tail2(self) -> bool:
        """<tail2> ::= '(' <round_part> ')' <tail1> | ε"""
        if self.ch == '(':
            if not self.match('('):
                return False
            if not self.round_part():
                return False
            if not self.match(')'):
                return False
            return self.tail1()
        # ε-правило
        return True

    def parse(self) -> bool:
        """Основной метод разбора"""
        if not self.expr():
            return False
        return self.ch is None


class AppState(Enum):
    """Состояния приложения"""
    PRINT_CONDITION = 1
    INPUT_EXPRESSION = 2
    EXIT = 3


def print_condition():
    """Выводит условие задачи"""
    print("\n" + "="*70)
    print("ПРАВИЛЬНАЯ СКОБОЧНАЯ ЗАПИСЬ С ДВУМЯ ВИДАМИ СКОБОК")
    print("="*70)
    print("Условие: Правильная скобочная запись с двумя видами скобок.")
    print("         Скобки одного вида не могут стоять рядом.")
    print("\nПравила грамматики:")
    print("  <expr> ::= <bracket_seq> | ε")
    print("  <bracket_seq> ::= '(' <round_part> ')' <tail1> | '[' <square_part> ']' <tail2>")
    print("  <round_part> ::= <bracket_seq> | ε")
    print("  <square_part> ::= <bracket_seq> | ε")
    print("  <tail1> ::= '[' <square_part> ']' <tail2> | ε")
    print("  <tail2> ::= '(' <round_part> ')' <tail1> | ε")
    print("\nПримеры правильных записей:")
    print("  • [(()[])](()[()])[()[[]()]]")
    print("  • ()")
    print("  • []")
    print("  • ([])[()]")
    print("\nПримеры неправильных записей:")
    print("  • [()([]([]()))]  # одинаковые скобки подряд")
    print("  • [)              # несоответствие типов скобок")
    print("  • (]              # несоответствие типов скобок")
    print("  • ([][()])        # квадратные скобки подряд")
    print("  • (())()          # круглые скобки подряд")
    print("\nДля выхода введите 'q'")
    print("="*70)


def process_expression(exp: str) -> None:
    """Обрабатывает введенное выражение"""
    if not exp:
        print("Ошибка: Пустая строка не была введена")
        return
    
    parser = Parser(exp)
    result = parser.parse()
    
    if result:
        print(f"Выражение '{exp}' РАСПОЗНАНО как правильное")
    else:
        print(f"Выражение '{exp}' НЕ РАСПОЗНАНО")


def main() -> None:
    """Основная функция приложения"""
    state = AppState.PRINT_CONDITION
    
    while state != AppState.EXIT:
        if state == AppState.PRINT_CONDITION:
            print_condition()
            state = AppState.INPUT_EXPRESSION
            
        elif state == AppState.INPUT_EXPRESSION:
            try:
                user_input = input("\nВведите выражение для анализа: ").strip()
                
                if user_input.lower() == 'q':
                    print("Завершение работы программы...")
                    state = AppState.EXIT
                    continue
                    
                process_expression(user_input)
                
            except EOFError:
                print("\nОбнаружен конец ввода. Завершение работы...")
                state = AppState.EXIT
            except KeyboardInterrupt:
                print("\n\nПрограмма прервана пользователем")
                state = AppState.EXIT
            except Exception as e:
                print(f"Произошла ошибка: {e}")
                state = AppState.INPUT_EXPRESSION


if __name__ == "__main__":
    if len(sys.argv) > 1:
        for arg in sys.argv[1:]:
            if arg == "--help" or arg == "-h":
                print_condition()
                sys.exit(0)
            else:
                process_expression(arg)
    else:
        main()