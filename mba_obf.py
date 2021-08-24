import numpy as np
import itertools, random
from sympy import *
from sympy.parsing.sympy_parser import parse_expr 
from luaparser import ast, astnodes

import sys
sys.setrecursionlimit(10000)

LUA_MODE = True
A_x_symbols = ['a_symbolic', 'b_symbolic', 'c_symbolic', 'd_symbolic', 'e_symbolic', 'f_symbolic']
RULE_DATABASE = [] # can be represented via much more efficient datastructure to do O(1) lookups

def egcd(a, b):
	if a == 0:
		return (b, 0, 1)
	else:
		g, y, x = egcd(b % a, a)
		return (g, x - (b // a) * y, y)

def modinv(a, m):
	g, x, y = egcd(a, m)
	if g != 1:
		return -1
	else:
		return x % m

class RandomModuloPolynomial():
	# first degree ax+b, but can be extended to any arbritrary degree
	def __init__(self, n, n_rand_offset):
		self.a = -1
		while self.a == -1:
			self.a = modinv(random.randrange(2**(n-n_rand_offset)), 2**n)
		self.b = random.randrange(2**(n-n_rand_offset))
		self.a_inv = modinv(self.a, 2**n)
		self.b_inv = -self.b*self.a_inv
		self.ast_tree = ast.parse("return (a_inv*(a*x + b) + b_inv) % " + str(2**n))

		for node in ast.walk(self.ast_tree):
			if isinstance(node, astnodes.Name):
				if node.id == "a":
					find_replace_node(self.ast_tree, node, astnodes.Number(self.a))
				elif node.id == "b":
					find_replace_node(self.ast_tree, node, astnodes.Number(self.b))
				elif node.id == "a_inv":
					find_replace_node(self.ast_tree, node, astnodes.Number(self.a_inv))
				elif node.id == "b_inv":
					find_replace_node(self.ast_tree, node, astnodes.Number(self.b_inv))
		print("RandomModuloPolynomial", self.a, self.b, self.a_inv, self.b_inv)

	def replace_x(self, x, direct_replace = False):
		for node in ast.walk(self.ast_tree):
			if isinstance(node, astnodes.Name):
				if node.id == "x":
					if direct_replace:
						find_replace_node(self.ast_tree, node, x)
					else:
						find_replace_node(self.ast_tree, node, x.ast_tree.body.body[0].values[0])
		return self

class ObfuscatedRule():
	def __init__(self, expressions, nullspace_result, readable_string):
		self.expressions = expressions
		self.expressions_lookup = {}
		expr_idx = 0
		for x in expressions:
			self.expressions_lookup[x.id] = (x, nullspace_result[expr_idx], expr_idx)
			expr_idx = expr_idx + 1
		self.nullspace_result = nullspace_result
		self.readable_string = readable_string
	def make_ast(self, readable_string=None):
		if readable_string == None:
			readable_string = self.readable_string
		self.ast_tree = ast.parse("return " + readable_string.replace('^', '~'))
		#print(self.readable_string.replace('^', '~'))
		#print(ast.to_lua_source(self.ast_tree))
		#print(ast.to_pretty_str(self.ast_tree))

class BinaryExpression():
	def __init__(self, id, expression_string, truth_table):
		self.id = id # allow for quick search
		self.expression_string = expression_string
		self.truth_table = truth_table
		self.ast_tree = ast.parse("return " + self.expression_string.replace('^', '~'))
		self.op_name = (type(self.ast_tree.body.body[0].values[0]).__name__)
		print("BinaryExpression:", id, self.op_name, expression_string)
		if truth_table is None:
			temp_expr = self.expression_string.replace('&', ' and ').replace('|', ' or ').replace('~', 'not ')
			temp_res = [None, None, None, None]
			temp_res[0] = eval(temp_expr, {"x": 0, "y": 0})
			temp_res[1] = eval(temp_expr, {"x": 0, "y": 1})
			temp_res[2] = eval(temp_expr, {"x": 1, "y": 0})
			temp_res[3] = eval(temp_expr, {"x": 1, "y": 1})
			for i in range(4):
				if type(temp_res[i])==bool:
					if temp_res[i]:
						temp_res[i] = 1
					else:
						temp_res[i] = 0
			self.truth_table = np.asarray(temp_res)
		print("-----")

def make_symbolic_string(A_x, M):
	M_idx = 0
	A_x_composed_expression = ""
	for A_x_instance in A_x:
		if (abs(M[M_idx]) > 0):
			M_idx_str = str(M[M_idx])
			A_x_str = A_x_symbols[M_idx]
			if A_x_instance.expression_string == "1":
				A_x_str = "1"
			elif A_x_instance.expression_string == "0":
				A_x_str = "0"

			if A_x_str == "1":
				A_x_str = "-1"
			if(M[M_idx] > 0) and A_x_composed_expression != "":
				M_idx_str = "+" + M_idx_str
			A_x_composed_expression = A_x_composed_expression + (M_idx_str + "*(" + A_x_str + ")")
		M_idx = M_idx + 1
	return A_x_composed_expression

def make_readable_string(A_x, M):
	M_idx = 0
	A_x_composed_expression = ""
	for A_x_instance in A_x:
		if (abs(M[M_idx]) > 0):
			M_idx_str = str(M[M_idx])
			A_x_str = A_x_instance.expression_string

			# string conv for language stuff and handle -1 case
			if A_x_str == "1":
				A_x_str = "-1"
			elif A_x_str == "x^y":
				if LUA_MODE:
					_x_str = "x~y"

			if(M[M_idx] > 0) and A_x_composed_expression != "":
				M_idx_str = "+" + M_idx_str
			A_x_composed_expression = A_x_composed_expression + (M_idx_str + "*(" + A_x_str + ")")
		M_idx = M_idx + 1
	return A_x_composed_expression

expressions = [BinaryExpression(1,"0", None), #0
			   BinaryExpression(2,"x&y", None), #xy
			   BinaryExpression(3,"x&~y", None), #xy'
			   BinaryExpression(4,"x", None), #x
			   BinaryExpression(5,"~x&y", None), #x'y
			   BinaryExpression(6,"y", None), #y
			   BinaryExpression(7,"x^y", None), #xy' + x'y
			   BinaryExpression(8,"x|y", None), #x + y
			   BinaryExpression(9,"~(x|y)", None), #(x+y)'
			   BinaryExpression(10,"(x&y)|(~x&~y)", None), #xy + x'y'
			   BinaryExpression(11,"~y", None), #y'
			   BinaryExpression(12,"x|~y", None), #x + y'
			   BinaryExpression(13,"~x", None), #x'
			   BinaryExpression(14,"~x|y", None), #x' + y
			   BinaryExpression(15,"~(x&y)", None), #(xy)'
			   BinaryExpression(16,"1", None), #1
			   ]

for i in range(5, 6):
	global_count = 0
	expression_combos = itertools.combinations(expressions, r=i)
	expression_combos = itertools.islice(expression_combos, global_count, None)

	A_expressions = [p for p in expression_combos]
	for A_x in A_expressions:
		A_columns = [None] * len(A_x)
		for ii in range(len(A_x)):
			A_columns[ii] = A_x[ii].truth_table
		A = np.asarray(A_columns).T
		M = Matrix(A)
		M = nsimplify(M,rational=True).nullspace()
		if (len(M) > 0):
			M = np.asarray(M[0].tolist()).flatten()
			M = M / np.min(abs(M[np.nonzero(M)]))
			global_count = global_count + 1
			if (global_count % 1000 == 0):
				print(global_count)
			M_nonzero_count = np.count_nonzero(M)
			if M_nonzero_count >= 3:
				print("------------", i, global_count)
				print("nullspace = ", M)
				print("nonzero elements = ", M_nonzero_count)
				A_x_composed_expression = make_readable_string(A_x, M)
				comp_expr_test = eval(A_x_composed_expression, {"x": 0, "y": 0})
				if not LUA_MODE:
					assert(comp_expr_test == 0)
				RULE_DATABASE.insert(len(RULE_DATABASE), ObfuscatedRule(A_x, M, A_x_composed_expression))
				print(A_x_composed_expression)
				#print(A)
				#print(M)

def find_add_sub_rule(a_sign, b_sign):
	for x in RULE_DATABASE:
		if (4 in x.expressions_lookup) and (6 in x.expressions_lookup):
			#print(x.expressions_lookup[4][1], x.expressions_lookup[6][1])
			if a_sign == x.expressions_lookup[4][1] and b_sign == x.expressions_lookup[6][1]:
				return x

def find_rule_id(id, id_2 = None):
	for x in RULE_DATABASE:
		if id_2 == None:
			if (id in x.expressions_lookup) and (x.expressions_lookup[id][1] == 1):
				return x
		else:
			if (id in x.expressions_lookup) and (x.expressions_lookup[id][1] == 1) and (id_2 in x.expressions_lookup) and (x.expressions_lookup[id_2][1] == 1):
				return x

def find_replace_node(tree, child, new_child):
	for node in ast.walk(tree):
		for k in node.__dict__:
			if (node.__dict__[k] == child):
				node.__dict__[k] = new_child
				return True
			elif (type(node.__dict__[k]) is list):
				for i, v in enumerate(node.__dict__[k]):
					if v == child:
						node.__dict__[k][i] = new_child
						return True

def find_parent_node(tree, child):
	for node in ast.walk(tree):
		for k in node.__dict__:
			if (node.__dict__[k] == child):
				return node
			elif (type(node.__dict__[k]) is list):
				for i, v in enumerate(node.__dict__[k]):
					if v == child:
						return node

def ast_expr_rewrite(tree, node, repl_expr):
	for inner_node in ast.walk(repl_expr.ast_tree):
		if isinstance(inner_node, astnodes.Name):
			if inner_node.id == "x":
				find_replace_node(repl_expr.ast_tree, inner_node, node.left)
			elif inner_node.id == "y":
				find_replace_node(repl_expr.ast_tree, inner_node, node.right)
			else:
				assert(False)
	find_replace_node(tree, node, repl_expr.ast_tree.body.body[0].values[0])

def ast_name_rewrite(tree, node, repl_expr, y_var):
	for inner_node in ast.walk(repl_expr.ast_tree):
		if isinstance(inner_node, astnodes.Name):
			if inner_node.id == "x":
				find_replace_node(repl_expr.ast_tree, inner_node, node.id)
			elif inner_node.id == "y":
				find_replace_node(repl_expr.ast_tree, inner_node, y_var)
			else:
				assert(False)
	find_replace_node(tree, node, repl_expr.ast_tree.body.body[0].values[0])

def obfuscate_constant(tree, node, rmp, tree_name_list):
	# generate M order polynomial and expand expression
	expr_id = 2
	repl_expr = find_rule_id(expr_id, 16)
	M_copy = repl_expr.nullspace_result.copy()
	rand_prime = randprime(1024, 4096)
	M_copy = M_copy * rand_prime
	print(rand_prime)
	print(repl_expr.nullspace_result)

	mba_expr_string = make_symbolic_string(repl_expr.expressions, M_copy) + "+" + str(node.n)
	poly_expr_string = (ast.to_lua_source(rmp.ast_tree.body.body[0].values[0]))
	simplified_expr_string = str(parse_expr(poly_expr_string.replace("x", mba_expr_string)))

	#print(make_readable_string(repl_expr.expressions, M_copy))
	#print(mba_expr_string)
	#print(poly_expr_string)
	#print(simplified_expr_string)

	for symbol_idx in range(len(repl_expr.expressions)):
		simplified_expr_string = simplified_expr_string.replace(A_x_symbols[symbol_idx], repl_expr.expressions[symbol_idx].expression_string)
	simplified_expr_string = simplified_expr_string.replace('^', '~')
	simplified_expr_string = simplified_expr_string.replace('Mod(', '(')
	simplified_expr_string = simplified_expr_string.replace(',', ')%(')

	# we can also do this symbolically with an expression replacement in the ast tree
	simplified_expr_string = simplified_expr_string.replace('x', random.choice(tree_name_list).id)
	simplified_expr_string = simplified_expr_string.replace('y', random.choice(tree_name_list).id)

	simplified_expr_ast = ast.parse("return " + simplified_expr_string)
	find_replace_node(tree, node, simplified_expr_ast.body.body[0].values[0])

AST_OP_TO_EXPR_ID = {astnodes.Number : 1, astnodes.Name : 4, astnodes.BAndOp : 2, astnodes.BXorOp : 7, astnodes.BOrOp : 8}

# is_locked = ((input~0x7777ABCD) | (~(input~0x7777ABCD) + 1))
init_src = """
	a = b + c
	"""

n_bits = 32
def perform_expr_rewrite(src):
	tree = ast.parse(src)
	print(ast.to_pretty_str(tree))

	tree_name_list = []
	constants_list = []
	originals_list = []

	for node in ast.walk(tree):
		if isinstance(node, astnodes.Name) and not (node in tree_name_list):
			tree_name_list.insert(0, node)
		if isinstance(node, astnodes.Number):
			constants_list.insert(0, node)
		originals_list.insert(0, node)

	for node in ast.walk(tree):
		print("Proc Node")
		rmp = RandomModuloPolynomial(n_bits, n_bits - 16)
		random.shuffle(RULE_DATABASE)
		if isinstance(node, astnodes.AddOp) or isinstance(node, astnodes.SubOp):
			is_add_op = isinstance(node, astnodes.AddOp)
			if is_add_op:
				repl_expr = find_add_sub_rule(1, 1)
			else:
				repl_expr = find_add_sub_rule(1, -1)

			x_idx = repl_expr.expressions_lookup[4][2]
			y_idx = repl_expr.expressions_lookup[6][2]
			M_copy = repl_expr.nullspace_result.copy()
			M_copy[x_idx] = 0
			M_copy[y_idx] = 0
			M_copy = -1 * M_copy
			repl_expr.make_ast(make_readable_string(repl_expr.expressions, M_copy))
			repl_expr = rmp.replace_x(repl_expr)
			ast_expr_rewrite(tree, node, repl_expr)
		else:
			if isinstance(node, astnodes.Number):
				print("Number detected in MBA pass, skipping")
				#obfuscate_constant(tree, node, rmp, tree_name_list)
			else:
				for ast_op_type, expr_id in AST_OP_TO_EXPR_ID.items():
					if isinstance(node, ast_op_type):
						repl_expr = find_rule_id(expr_id)
						M_copy = repl_expr.nullspace_result.copy()
						M_copy[repl_expr.expressions_lookup[expr_id][2]] = 0
						M_copy = -1 * M_copy
						repl_expr.make_ast(make_readable_string(repl_expr.expressions, M_copy))
						repl_expr = rmp.replace_x(repl_expr)
						if isinstance(node, astnodes.Name):
							if isinstance(find_parent_node(tree, node), astnodes.Assign) and not (node in find_parent_node(tree, node).targets):
								ast_name_rewrite(tree, node, repl_expr, random.choice(tree_name_list))
						else:
							ast_expr_rewrite(tree, node, repl_expr)

	for node in ast.walk(tree):
		random.shuffle(RULE_DATABASE)
		if node in constants_list:
			rmp = RandomModuloPolynomial(n_bits, n_bits - 16)
			obfuscate_constant(tree, node, rmp, tree_name_list)
			# print("const obf disabled")

	obf_src = ast.to_lua_source(tree)
	#print(ast.to_pretty_str(tree))
	print(obf_src)
	return obf_src

src = init_src
for i in range(2):
	src = perform_expr_rewrite(src)