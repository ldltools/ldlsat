all:
	@echo "try 'make test' to solve pigeon hole problems using shelltest"

clean:;	rm -f *~
test:
	@echo "** ldlsat **"
	time shelltest phole.conf
	@echo; echo "** z3 **"
	time shelltest phole_z3.conf
