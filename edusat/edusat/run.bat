for %%f in (test\sat\*.cnf) do (
..\release\edusat %1 %%f 
)
for %%f in (test\unsat\*.cnf) do (
..\release\edusat %1 %%f 
)