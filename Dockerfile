FROM debian:stable-slim as builder
MAINTAINER LDL Tools development team <ldltools@outlook.com>

ENV DEBIAN_FRONTEND noninteractive
ENV DEBIAN_PRIORITY critical
ENV DEBCONF_NOWARNINGS yes

RUN echo "dash dash/sh boolean false" | debconf-set-selections;\
    dpkg-reconfigure -f noninteractive dash;\
    echo "/usr/local/lib" > /etc/ld.so.conf.d/usr-local-lib.conf
RUN apt-get update;\
    apt-get install -y build-essential flex bison gawk file rsync

# mona
WORKDIR /root
RUN apt-get install -y wget;\
    wget -q http://www.brics.dk/mona/download/mona-1.4-17.tar.gz;\
    tar xzf mona-1.4-17.tar.gz;\
    (cd mona-1.4; ./configure --prefix=/usr/local && make && make install-strip);\
    ldconfig

# ocaml
RUN apt-get install -y opam;\
    opam init -y;\
    opam switch -y 4.07.0;\
    touch /root/.bash_profile && cat /root/.opam/opam-init/init.sh >> /root/.bash_profile

# ldlsat
ADD . /root/ldlsat
WORKDIR /root/ldlsat
RUN eval `opam config env`;\
    opam install -y ocamlfind ppx_deriving ppx_deriving_yojson;\
    make veryclean && make && make PREFIX=/usr/local install

WORKDIR /root
CMD ["/bin/bash"]

# ====================
# final image
# ====================
#FROM alpine:latest
FROM debian:stable-slim

RUN echo "dash dash/sh boolean false" | debconf-set-selections;\
    dpkg-reconfigure -f noninteractive dash;\
    echo "/usr/local/lib" > /etc/ld.so.conf.d/usr-local-lib.conf
RUN apt-get update;\
    apt-get install -y gawk

WORKDIR /usr/local
COPY --from=builder /usr/local .
RUN ldconfig

WORKDIR /root
CMD ["/bin/bash"]
