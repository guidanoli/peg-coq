## Cronograma

- Definir PEGs sem gramática (char, ., vazio, sequencia, choice, kleene, !)
- Definir match (small step [predicado], função usando gas)
- Tentar provar (se a função aceita com algum gas, o predicado aceita)
- Definir predicado que uma pattern pode casar vazio (não consome nada)
- Provar que esse predicado é correto (que existe o match [predicado] existe)
- Definir função equivalente a esse predicado
- Provar equivalência entre essas duas definições
- Definir WF usando esse predicado (não existe repetição de pattern que pode não consumir nada)
- Definir função para esse WF
- Provar que WF é correto (se é WF, o predicado sempre dá uma resposta [match ou fail])
