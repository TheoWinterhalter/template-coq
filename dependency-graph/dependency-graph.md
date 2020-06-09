# Generate the dependency graph between files

1. In each folder (template-coq + checker + pcuic + safechecker + extraction), generate the dot file with:
```
coqdep -f _CoqProject -dumpgraph plop.dot > /dev/null
```

2. Add the colors at nodes in each plop.dot with the following find-and-replace:
```
]  ->  , color=blue]
```
The list of colors is there:
https://graphviz.gitlab.io/_pages/doc/info/colors.html

3. Concatenate all files plop.dot into one and add the following after the first line:
```
node[style=filled]
```

4. Now, you have to remove double edges. I did in Python 3:
```
f=open("plop.dot")
l=f.readlines()
s=set(l[2:-1])
for x in s:
	print(x, end='')
```
then copy and paste.

5. Generate the svg/pdf/png:
```
dot -Tsvg plop.dot -o plop.svg
dot -Tpdf plop.dot -o plop.pdf
dot -Tpng plop.dot -o plop.png
```
