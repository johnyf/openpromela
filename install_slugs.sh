# installation script for slugs
# on Linux and Darwin
#
# https://github.com/LTLMoP/slugs
set -e

INSTALL=/usr/local/bin

# have macports ?
if hash port >/dev/null 2>&1; then
	echo "found macports"
	have_macports=true
else
	echo "macports not found"
fi

# dependencies
if [[ "$(uname)" = "Darwin" ]] && [[ "$have_macports" = "true" ]]
then
	sudo port install boost
	sudo port install qt4-mac
	# sudo port install libGLU
	# sudo port install libcudd
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]
then
	sudo add-apt-repository -y ppa:ubuntu-toolchain-r/test  # gcc v4.8
	sudo apt-get -qq update
	sudo apt-get install curl
	sudo apt-get install qt4-qmake libglu-dev
	sudo apt-get -qq install g++-4.8
	sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-4.8 90
	sudo apt-get install -qq libboost-all-dev
	sudo apt-get install -qq libboost-dbg
	sudo apt-get -y install gdb
fi

g++ -v
gdb -v

# fetch slugs
if ! [ -d "slugs" ] ; then
	git clone https://github.com/LTLMoP/slugs
fi
cd slugs/

# fetch CUDD
cd lib/
if ! [ -d "cudd-2.5.0" ] ; then
	curl -LO ftp://vlsi.colorado.edu/pub/cudd-2.5.0.tar.gz
	tar -xzf cudd-2.5.0.tar.gz
	cd cudd-2.5.0
	# build CUDD
	patch Makefile ../../tools/CuddMakefile.patch
	if [ "$(uname)" == "Darwin" ] ; then
		patch -p0 < ../../tools/CuddOSXFixes.patch
	fi
	make
	cd ../
fi
cd ../

# build slugs
cd src/
if ! [ -e "slugs" ] ; then
	qmake Tool.pro
	make
fi
sudo cp slugs "${INSTALL}/slugs"
ls /usr/local/bin/
echo $PATH

# check success
if hash slugs >/dev/null 2>&1; then
	echo "slugs successfully installed at ${INSTALL}"
else
	echo "slugs failed to install"
	exit 1
fi

cd ../../

