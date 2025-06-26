from sympy import symbols, exp, Piecewise

# Define the variable and parameter
x, lam = symbols('x lambda', real=True, positive=True)

# Exponential distribution PDF: f(x) = lambda * exp(-lambda * x) for x >= 0
pdf = Piecewise(
    (lam * exp(-lam * x), x >= 0),
    (0, True)
)

print("Exponential distribution PDF:")
print(pdf)