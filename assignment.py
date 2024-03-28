from collections import defaultdict

def negate(literal):
  """Negates a literal (atom or its negation)."""
  return "~" + literal if not literal.startswith("~") else literal[1:]

def eliminate_implication(formula):
  """Eliminates implication using De Morgan's Law."""
  if "=>" in formula:
    parts = formula.split("=>")
    return "~(" + parts[0] + ") & " + parts[1]
  return formula

def move_negation_inward(formula):
  """Moves negation inwards using De Morgan's Law."""
  operators = ["&", "|"]
  if any(op in formula for op in operators):
    parts = formula.split()
    new_parts = []
    for part in parts:
      if part.startswith("~"):
        if part[1] in operators:
          inner = part[2:].split(")")[-1]
          new_parts.append("(" + move_negation_inward(inner) + ")")
        else:
          new_parts.append(part)
      else:
        new_parts.append(part)
    return " ".join(new_parts)
  return formula

def standardize_variables(formula, prefix="v"):
  """Standardizes variable names by adding a prefix."""
  new_formula = ""
  i = 0
  for char in formula:
    if char.islower() and char.isalpha():
      new_formula += prefix + str(i)
      i += 1
    else:
      new_formula += char
  return new_formula

def prenex_normal_form(formula):
    """Converts formula to prenex normal form."""

    if not any(quantifier in formula for quantifier in ["∀", "∃"]):
        return formula  # Already in prenex form

    quantifier_index = max([formula.index(q) for q in ["∀", "∃"] if q in formula])
    matrix = formula[quantifier_index + 2:]
    prefix = formula[:quantifier_index + 2]

    while any(quantifier in matrix for quantifier in ["∀", "∃"]):
        inner_quantifier_index = min([matrix.index(q) for q in ["∀", "∃"] if q in matrix])
        inner_quantifier = matrix[inner_quantifier_index]
        inner_matrix = matrix[inner_quantifier_index + 2:]
        inner_prefix = matrix[:inner_quantifier_index + 2]
        matrix = inner_matrix
        prefix = inner_prefix + prefix

    return prefix + "(" + matrix + ")"


def skolemization(formula):
    """Applies Skolemization for existential quantifiers."""

    if "∃" not in formula:
        return formula  # No existential quantifiers

    def skolemize_subformula(subformula):
        if any(q in subformula for q in ["∀", "∃"]):
            quantifier_index = min([subformula.index(q) for q in ["∀", "∃"] if q in subformula])
            quantifier = subformula[quantifier_index]
            matrix = subformula[quantifier_index + 2:]
            prefix = subformula[:quantifier_index + 2]
            if quantifier == "∃":
                variable = matrix[1]
                skolem_constant = "c" + variable  # Simple skolemization
                return prefix + skolem_constant
            else:
                return prefix + "(" + skolemize_subformula(matrix) + ")"
        else:
            return subformula

    return skolemize_subformula(formula)
def eliminate_universal_quantifiers(formula):
    """Eliminates universal quantifiers."""

    if "∀" not in formula:
        return formula  # No universal quantifiers

    while "∀" in formula:
        quantifier_index = formula.index("∀")
        variable = formula[quantifier_index + 2]
        matrix = formula[quantifier_index + 4:]
        prefix = formula[:quantifier_index]
        formula = prefix + "(" + matrix.replace(variable, "_") + ")"  # Replace with dummy variable

    return formula


def conjunctive_normal_form(formula):
  """Converts formula to conjunctive normal form (CNF)."""
  if "&" in formula:
    return " & ".join([conjunctive_normal_form(part) for part in formula.split("&")])
  return formula

def split_to_clauses(formula):
  """Splits formula into a set of clauses in CNF."""
  if "|" in formula:
    return {clause for part in formula.split("|") for clause in split_to_clauses(part)}


  return {formula}

def rename_variables(clauses, prefix="v"):
  """Renames variables in each clause to avoid conflicts."""
  variable_map = defaultdict(int)
  new_clauses = set()
  for clause in clauses:
    new_clause = []
    for literal in clause.split():
      if literal.islower() and literal.isalpha():
        var = literal
        count = variable_map[var]
        new_var = prefix + str(count)
        variable_map[var] += 1
        new_clause.append(new_var if var == literal else literal.replace(var, new_var))
      else:
        new_clause.append(literal)
    new_clauses.add(" ".join(new_clause))
  return new_clauses

# Example usage
formula = "(A => B) & (C | ~D)"
formula = eliminate_implication(formula)
formula = move_negation_inward(formula)
formula = standardize_variables(formula)
cnf = conjunctive_normal_form(formula)
clauses = split_to_clauses(cnf)
renamed_clauses = rename_variables(clauses)

print("Original formula:", formula)
print("CNF:", cnf)
print("Clauses:", renamed_clauses)

