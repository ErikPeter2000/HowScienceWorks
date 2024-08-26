# How Science Works

This is my homework for the How Science Works practical as part of the OCR A-level Physics course. Here, I investigate which boolean satisfaction problems are the hardest to solve. The intended audience is my physics teacher.

After further investigation, I found that my results were completely wrong due to a bug. At the time of writing, I haven't amended the report, as I don't think that it's worth the time and the correction would probably go over the 3-page limit (which is already exceeded with references).

[Here is the report](LaTeX/HowScienceWorks.pdf). 

## Project Structure

- `LaTeX/`: Contains the LaTeX source code for the report.
- `PythonCode/`: Contains the Python Jupyter notebook used to process the data, and some old algorithms I wrote to solve the problems.
- `RustCode/`: Contains the Rust source code for the DPLL and WalkSAT algorithms used to solve the problems. The csv data used is [RustCode/results_more.csv](RustCode/results_more.csv).