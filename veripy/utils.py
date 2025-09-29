import ast

def read_code_from_file(filename: str) -> str:
    with open(filename, 'r') as file:
        content = file.read()

    return content

def get_function_ast(code_text: str, func_name: str) -> ast.FunctionDef:
    """
    Parse code_text and return the AST node for the function named func_name.
    
    Raises ValueError if function is not found.
    """
    parsed = ast.parse(code_text)
    for node in ast.walk(parsed):
        if isinstance(node, ast.FunctionDef) and node.name == func_name:
            return node

    raise ValueError(f"Function '{func_name}' not found in code.")