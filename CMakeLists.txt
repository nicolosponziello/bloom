set(COMPONENT_NAME "bloom")
set(COMPONENT_SRCS "bloom.c" )
set(COMPONENT_ADD_INCLUDEDIRS ".")

idf_component_register(SRCS ${COMPONENT_SRCS}
                        INCLUDE_DIRS ${COMPONENT_ADD_INCLUDEDIRS})