from setuptools import setup, find_packages

setup(
    name="veripy",
    version="0.1.0",
    description="A verification system for Python programs",
    author="Veripy Team",
    packages=find_packages(),
    python_requires=">=3.8",
    install_requires=[
        "z3-solver",
    ],
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Developers",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Programming Language :: Python :: 3.12",
        "Programming Language :: Python :: 3.13",
    ],
)
