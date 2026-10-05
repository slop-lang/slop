"""Tests for OpenAPI to SLOP conversion"""

import json

import pytest
from slop.schema_converter import (
    OpenApiConverter, SlopFunction, convert_openapi, detect_schema_format
)

from derive_helpers import (
    FIXTURES, REPO, add_main, assert_checks, build_and_run, derive, fill_holes,
    requires_native, slop,
)


class TestSchemaFormatDetection:
    """Tests for detect_schema_format function"""

    def test_detect_openapi3(self):
        spec = {"openapi": "3.0.0", "paths": {}}
        assert detect_schema_format(spec) == "openapi"

    def test_detect_swagger2(self):
        spec = {"swagger": "2.0", "paths": {}}
        assert detect_schema_format(spec) == "swagger"

    def test_detect_openapi_by_paths(self):
        spec = {"paths": {"/users": {}}}
        assert detect_schema_format(spec) == "openapi"

    def test_detect_jsonschema(self):
        spec = {"type": "object", "properties": {}}
        assert detect_schema_format(spec) == "jsonschema"


class TestOpenApiConverter:
    """Tests for OpenApiConverter class"""

    def test_simple_get_endpoint(self):
        spec = {
            "openapi": "3.0.0",
            "info": {"title": "Test API"},
            "paths": {
                "/users/{id}": {
                    "get": {
                        "summary": "Get user",
                        "parameters": [{
                            "name": "id",
                            "in": "path",
                            "required": True,
                            "schema": {"type": "integer", "minimum": 1}
                        }],
                        "responses": {
                            "200": {
                                "content": {
                                    "application/json": {
                                        "schema": {"$ref": "#/components/schemas/User"}
                                    }
                                }
                            }
                        }
                    }
                }
            },
            "components": {
                "schemas": {
                    "User": {
                        "type": "object",
                        "properties": {
                            "id": {"type": "integer"},
                            "name": {"type": "string"}
                        }
                    }
                }
            }
        }

        output = OpenApiConverter().convert(spec)

        # Check function name
        assert "get-users-by-id" in output
        # Check parameter type
        assert "(Int 1 ..)" in output
        # Check precondition from minimum
        assert "(@pre (>= id 1))" in output
        # Check complexity tier
        assert ":complexity tier-1" in output

    def test_post_with_request_body(self):
        spec = {
            "openapi": "3.0.0",
            "info": {"title": "Test"},
            "paths": {
                "/users": {
                    "post": {
                        "summary": "Create user",
                        "requestBody": {
                            "content": {
                                "application/json": {
                                    "schema": {"$ref": "#/components/schemas/CreateUser"}
                                }
                            }
                        },
                        "responses": {
                            "201": {
                                "content": {
                                    "application/json": {
                                        "schema": {"$ref": "#/components/schemas/User"}
                                    }
                                }
                            }
                        }
                    }
                }
            },
            "components": {
                "schemas": {
                    "User": {"type": "object", "properties": {"id": {"type": "integer"}}},
                    "CreateUser": {"type": "object", "properties": {"name": {"type": "string"}}}
                }
            }
        }

        output = OpenApiConverter(storage_mode='none').convert(spec)

        # Check function name uses 'create' prefix
        assert "create-users" in output
        # Check body parameter
        assert "(body (Ptr CreateUser))" in output
        # Check precondition for body
        assert "(@pre (!= body nil))" in output
        # Check context
        assert ":context (body)" in output

    def test_error_type_generation(self):
        spec = {
            "openapi": "3.0.0",
            "info": {"title": "Test"},
            "paths": {
                "/users/{id}": {
                    "get": {
                        "parameters": [{
                            "name": "id",
                            "in": "path",
                            "schema": {"type": "integer"}
                        }],
                        "responses": {
                            "200": {"description": "OK"},
                            "400": {"description": "Bad request"},
                            "404": {"description": "Not found"},
                            "500": {"description": "Server error"}
                        }
                    }
                }
            }
        }

        output = OpenApiConverter().convert(spec)

        # Check ApiError enum is generated
        assert "(type ApiError" in output
        assert "bad-request" in output
        assert "not-found" in output
        assert "internal-error" in output

    def test_example_extraction(self):
        spec = {
            "openapi": "3.0.0",
            "info": {"title": "Test"},
            "paths": {
                "/users/{id}": {
                    "get": {
                        "parameters": [{
                            "name": "id",
                            "in": "path",
                            "schema": {"type": "integer"},
                            "example": 42
                        }],
                        "responses": {
                            "200": {
                                "content": {
                                    "application/json": {
                                        "schema": {
                                            "type": "object",
                                            "properties": {
                                                "id": {"type": "integer"},
                                                "name": {"type": "string"}
                                            },
                                            "required": ["id", "name"]
                                        },
                                        "example": {"id": 42, "name": "Alice"}
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        output = OpenApiConverter(storage_mode='none').convert(spec)

        # The argument list is parenthesized even for one argument, and the
        # expected record is written as a constructor of its type.
        assert (
            '(@example (42) -> (ok (record-new GetUsersByIdResponse '
            '(id 42) (name "Alice"))))' in output
        )

    def test_no_nil_postcondition_for_record_response(self):
        spec = {
            "openapi": "3.0.0",
            "info": {"title": "Test"},
            "paths": {
                "/users/{id}": {
                    "get": {
                        "parameters": [{
                            "name": "id",
                            "in": "path",
                            "schema": {"type": "integer"}
                        }],
                        "responses": {
                            "200": {
                                "content": {
                                    "application/json": {
                                        "schema": {"$ref": "#/components/schemas/User"}
                                    }
                                }
                            }
                        }
                    }
                }
            },
            "components": {
                "schemas": {
                    "User": {"type": "object", "properties": {"id": {"type": "integer"}}}
                }
            }
        }

        output = OpenApiConverter().convert(spec)

        # A record result is a value, never nil, so (!= val nil) would compare
        # a struct with a null pointer. No postcondition is emitted for it.
        assert "(!= val nil)" not in output
        assert "@post" not in output

    def test_postcondition_for_list_response(self):
        spec = {
            "openapi": "3.0.0",
            "info": {"title": "Test"},
            "paths": {
                "/users": {
                    "get": {
                        "responses": {
                            "200": {
                                "content": {
                                    "application/json": {
                                        "schema": {
                                            "type": "array",
                                            "items": {"$ref": "#/components/schemas/User"}
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            },
            "components": {
                "schemas": {
                    "User": {"type": "object", "properties": {"id": {"type": "integer"}}}
                }
            }
        }

        output = OpenApiConverter().convert(spec)

        # The postcondition measures the list with list-len. `len` is not a
        # builtin in the checker, the transpiler or the runtime, and `list` is
        # a reserved form name, so the old spelling could not compile (#83).
        assert "@post" in output
        assert "(list-len xs)" in output
        assert "(len list)" not in output

    def test_operation_tier_assignment(self):
        spec = {
            "openapi": "3.0.0",
            "info": {"title": "Test"},
            "paths": {
                "/users/{id}": {
                    "get": {
                        "parameters": [{"name": "id", "in": "path", "schema": {"type": "integer"}}],
                        "responses": {"200": {"description": "OK"}}
                    },
                    "put": {
                        "parameters": [{"name": "id", "in": "path", "schema": {"type": "integer"}}],
                        "requestBody": {"content": {"application/json": {"schema": {"type": "object"}}}},
                        "responses": {"200": {"description": "OK"}}
                    },
                    "delete": {
                        "parameters": [{"name": "id", "in": "path", "schema": {"type": "integer"}}],
                        "responses": {"204": {"description": "Deleted"}}
                    }
                },
                "/users": {
                    "get": {
                        "parameters": [{"name": "limit", "in": "query", "schema": {"type": "integer"}}],
                        "responses": {"200": {"description": "OK"}}
                    }
                }
            }
        }

        output = OpenApiConverter().convert(spec)

        # GET by ID should be tier-1
        assert ":complexity tier-1" in output
        # PUT should be tier-3
        assert ":complexity tier-3" in output
        # DELETE should be tier-2
        assert ":complexity tier-2" in output

    def test_reuses_json_schema_converter(self):
        spec = {
            "openapi": "3.0.0",
            "info": {"title": "Test"},
            "paths": {},
            "components": {
                "schemas": {
                    "User": {
                        "type": "object",
                        "properties": {
                            "id": {"type": "integer", "minimum": 1},
                            "name": {"type": "string", "minLength": 1, "maxLength": 100},
                            "age": {"type": "integer", "minimum": 0, "maximum": 150}
                        },
                        "required": ["id", "name"]
                    }
                }
            }
        }

        output = OpenApiConverter().convert(spec)

        # Check that component schema is converted with range types
        assert "(type User" in output
        assert "(Int 1 ..)" in output
        assert "(String 1 .. 100)" in output
        assert "(Option (Int 0 .. 150))" in output


class TestSlopFunctionOutput:
    """Tests for SlopFunction to_slop output"""

    def test_function_with_all_annotations(self):
        fn = SlopFunction(
            name="get-user",
            params=[("id", "(Int 1 ..)")],
            return_type="(Result User ApiError)",
            intent="Get user by ID",
            hole_prompt="Fetch user from storage",
            hole_tier="tier-1",
            context=["id"],
            preconditions=["(>= id 1)"],
            postconditions=["(match $result ((ok u) (!= u nil)) ((error _) true))"],
            examples=[(["42"], "(ok user-42)")]
        )

        output = fn.to_slop()

        assert "(fn get-user ((id (Int 1 ..)))" in output
        assert '(@intent "Get user by ID")' in output
        assert "(@spec (((Int 1 ..)) -> (Result User ApiError)))" in output
        assert "(@pre (>= id 1))" in output
        assert "(@post (match $result" in output
        assert "(@example (42) -> (ok user-42))" in output
        assert ':complexity tier-1' in output
        assert ':context (id)' in output

    def test_function_without_optional_annotations(self):
        fn = SlopFunction(
            name="simple-fn",
            params=[("x", "Int")],
            return_type="Int",
            intent="Simple function",
            hole_prompt="Do something",
            hole_tier="tier-1"
        )

        output = fn.to_slop()

        assert "(fn simple-fn ((x Int))" in output
        assert "@pre" not in output
        assert "@post" not in output
        assert "@example" not in output
        assert ":required" not in output


class TestStorageModes:
    """Tests for storage mode options"""

    def _get_petstore_spec(self):
        return {
            "openapi": "3.0.0",
            "info": {"title": "Pet Store"},
            "paths": {
                "/pets": {
                    "get": {
                        "summary": "List pets",
                        "responses": {"200": {"description": "OK"}}
                    },
                    "post": {
                        "summary": "Create pet",
                        "requestBody": {
                            "content": {
                                "application/json": {
                                    "schema": {"$ref": "#/components/schemas/NewPet"}
                                }
                            }
                        },
                        "responses": {"201": {"description": "Created"}}
                    }
                },
                "/pets/{id}": {
                    "get": {
                        "summary": "Get pet",
                        "parameters": [{
                            "name": "id",
                            "in": "path",
                            "schema": {"type": "integer", "minimum": 1}
                        }],
                        "responses": {"200": {"description": "OK"}}
                    }
                }
            },
            "components": {
                "schemas": {
                    "Pet": {"type": "object", "properties": {"id": {"type": "integer"}}},
                    "NewPet": {"type": "object", "properties": {"name": {"type": "string"}}}
                }
            }
        }

    def test_stub_mode_generates_requires(self):
        spec = self._get_petstore_spec()
        output = OpenApiConverter(storage_mode='stub').convert(spec)

        # Check @requires block is generated
        assert "(@requires storage" in output
        assert ':prompt "Which storage approach for this API?"' in output
        assert ":options" in output
        # Check storage function signatures
        assert "state-get-pet" in output
        assert "state-list-pets" in output
        assert "state-insert-pet" in output
        # Check functions have state parameter
        assert "(state (Ptr State))" in output
        # Check must-use includes storage function
        assert "state-get-pet" in output

    def test_map_mode_generates_state_types(self):
        spec = self._get_petstore_spec()
        output = OpenApiConverter(storage_mode='map').convert(spec)

        # Check State type is generated
        assert "(type PetId (Int 1 ..))" in output
        assert "(type State (record" in output
        assert "(pets (Map PetId Pet))" in output
        assert "(next-pet-id PetId)" in output
        # Check state-new function
        assert "fn state-new" in output
        # Check CRUD functions
        assert "fn state-get-pet" in output
        assert "fn state-list-pets" in output
        assert "fn state-insert-pet" in output
        assert "fn state-delete-pet" in output
        # No @requires block in map mode
        assert "(@requires storage" not in output

    def test_generated_storage_calls_only_real_builtins(self):
        """derive must not emit builtins the compiler does not have (#83).

        `map-empty` was emitted by state-new and has never existed in the
        checker, the transpiler or the runtime. `map-values` was emitted by
        state-list-*; it has a for-each element-type helper and a runtime
        macro, but no checker entry and no lowering, so it is not callable.
        `len` in the generated @post is not a builtin either.

        The result was that `slop derive --storage map` could not produce a
        module that even type-checks.
        """
        spec = self._get_petstore_spec()
        output = OpenApiConverter(storage_mode='map').convert(spec)

        assert "map-empty" not in output
        assert "map-values" not in output
        # `len` only ever appeared as the bare call; list-len is the builtin.
        assert "(len " not in output

        # state-new builds the map with the real constructor.
        assert "(map-new arena PetId Pet)" in output
        # Listing walks the keys and reads each value, using builtins that
        # exist. It allocates, so it takes the arena and is not @pure.
        assert "(map-keys (. state pets))" in output
        assert "(map-get (. state pets) k)" in output
        assert "fn state-list-pets ((arena Arena) (state (Ptr State))" in output

    def test_list_operations_thread_an_arena(self):
        """A collection GET allocates, so the arena reaches it (#83).

        state-list-* builds a new (List T) out of the map. Before, it claimed
        to be @pure and took no arena, which only worked because the builtin it
        called did not exist. The declared storage contract and the handler
        signature have to agree with the implementation.
        """
        spec = self._get_petstore_spec()

        stub = OpenApiConverter(storage_mode='stub').convert(spec)
        assert (
            "(state-list-pets ((arena Arena) (state (Ptr State)) "
            "(limit (Option Int)))" in stub
        )

        mapped = OpenApiConverter(storage_mode='map').convert(spec)
        # The collection GET handler gets the arena and offers it to the hole.
        assert "fn get-pets ((arena Arena) (state (Ptr State))" in mapped
        assert ":context (arena state state-list-pets)" in mapped
        # A single-item GET still does not allocate, so it gains nothing.
        assert "fn get-pets-by-id ((state (Ptr State))" in mapped

    def test_none_mode_no_storage_context(self):
        spec = self._get_petstore_spec()
        output = OpenApiConverter(storage_mode='none').convert(spec)

        # No @requires block
        assert "(@requires" not in output
        # No state type
        assert "(type State" not in output
        # No state parameter in functions
        assert "(state (Ptr State))" not in output
        # Functions just have their regular parameters
        assert "(fn get-pets-by-id ((id (Int 1 ..)))" in output

    def test_stub_mode_is_default(self):
        spec = self._get_petstore_spec()
        output = OpenApiConverter().convert(spec)

        # Default should be stub mode
        assert "(@requires storage" in output


def _petstore():
    return json.loads((FIXTURES / "petstore.json").read_text())


class TestOpenApiOutputShape:

    def test_output_is_a_module_with_exports(self):
        out = OpenApiConverter(storage_mode='none').convert(_petstore(), module_name="pets")
        assert out.startswith(";; Generated by slop derive from OpenAPI\n(module pets\n")
        start = out.index("(export")
        exports = out[start + len("(export"):out.index(")", start)].split()
        for name in ("Pet", "NewPet", "Error", "ApiError", "get-api-v1-pets-by-pet-id",
                     "get-health"):
            assert name in exports
        # Without a module name it is the kebab-case of the title.
        assert "(module pet-store-api\n" in OpenApiConverter().convert(_petstore())

    def test_stub_mode_defines_state(self):
        out = OpenApiConverter(storage_mode='stub').convert(_petstore())
        assert "(type State (record))" in out
        assert "(type PetId (Int 1 ..))" in out

    def test_resource_is_the_last_meaningful_segment(self):
        # /api/v1/pets used to make the resource `Api`, from the first segment.
        out = OpenApiConverter(storage_mode='map').convert(_petstore())
        assert "state-get-pet" in out
        assert "(pets (Map PetId Pet))" in out
        assert "state-get-api" not in out and "ApiId" not in out
        # /health returns one record and takes no id: not a stored resource.
        assert "(fn get-health ()" in out
        assert "HealthId" not in out

    def test_intent_and_prompt_are_escaped(self):
        out = OpenApiConverter(storage_mode='none').convert(_petstore())
        assert '(@intent "Create a \\"pet\\" \\\\ with quotes")' in out
        spec = _petstore()
        spec["paths"]["/api/v1/pets"]["get"]["summary"] = 'Line one\nline "two"'
        out = OpenApiConverter(storage_mode='none').convert(spec)
        assert '(@intent "Line one line \\"two\\"")' in out

    def test_example_renders_against_the_return_type(self):
        out = OpenApiConverter(storage_mode='none').convert(_petstore())
        # An enum variant, an Option payload, an absent optional field as
        # (none). A list field is `_` (a container in a record compares by
        # identity), and so is a ranged String, which slop test cannot yet
        # compare as a field.
        assert (
            "(@example (42) -> (ok (record-new Pet (id 42) (name _) (species 'cat) "
            "(weight (some 4.5)) (tags _) (born-at (none)))))"
        ) in out
        # A plain String is written out, escaped.
        spec = _petstore()
        del spec["components"]["schemas"]["Pet"]["properties"]["name"]["maxLength"]
        del spec["components"]["schemas"]["Pet"]["properties"]["name"]["minLength"]
        out = OpenApiConverter(storage_mode='none').convert(spec)
        assert '(name "Fluffy \\"the cat\\"")' in out

    def test_examples_omitted_when_state_is_a_parameter(self):
        # The spec's example assumes a stored pet; a fresh State has none.
        for mode in ('stub', 'map'):
            out = OpenApiConverter(storage_mode=mode).convert(_petstore())
            assert "@example" not in out

    def test_example_omitted_when_not_expressible(self):
        spec = _petstore()
        get = spec["paths"]["/api/v1/pets/{petId}"]["get"]
        get["responses"]["200"]["content"]["application/json"]["example"]["species"] = "lizard"
        out = OpenApiConverter(storage_mode='none').convert(spec)
        assert "@example" not in out

    def test_no_example_for_a_list_result(self):
        spec = _petstore()
        listing = spec["paths"]["/api/v1/pets"]["get"]
        listing["responses"]["200"]["content"]["application/json"]["example"] = [
            {"id": 1, "name": "A", "species": "dog"}]
        out = OpenApiConverter(storage_mode='none').convert(spec)
        # A list result cannot be compared without :eq.
        assert "(fn get-api-v1-pets ((limit (Option (Int 1 .. 100))))" in out
        assert "(@example (10)" not in out

    def test_component_named_api_error_does_not_collide(self):
        spec = _petstore()
        spec["components"]["schemas"]["ApiError"] = {
            "type": "string", "enum": ["conflict", "teapot"]}
        out = OpenApiConverter(storage_mode='none').convert(spec)
        assert "(type ApiError (enum bad-request not-found conflict" in out
        assert "(type ApiError2 (enum api-error2-conflict teapot))" in out

    def test_convert_openapi_honours_storage_mode(self):
        path = str(FIXTURES / "petstore.json")
        assert "(fn state-new" in convert_openapi(path, storage_mode='map', warnings=[])
        assert "(@requires storage" in convert_openapi(path, warnings=[])
        assert "(state (Ptr State))" not in convert_openapi(path, storage_mode='none',
                                                              warnings=[])

    def test_unknown_storage_mode_is_an_error(self):
        with pytest.raises(ValueError):
            OpenApiConverter(storage_mode='sql')

    def test_swagger_2_definitions_and_body(self):
        spec = {
            "swagger": "2.0",
            "info": {"title": "T"},
            "paths": {"/items": {"post": {
                "parameters": [{"name": "item", "in": "body",
                                "schema": {"$ref": "#/definitions/Item"}}],
                "responses": {"200": {"schema": {"$ref": "#/definitions/Item"}}}}}},
            "definitions": {"Item": {"type": "object",
                                     "properties": {"id": {"type": "integer"}}}},
        }
        out = OpenApiConverter(storage_mode='none').convert(spec)
        assert "(fn create-items ((body (Ptr Item)))" in out
        assert "(Result Item ApiError)" in out


@requires_native
class TestDerivedOpenApiBuilds:
    """Each storage mode's output checks (holes aside) and, holes filled, builds."""

    @pytest.mark.parametrize("spec", [
        FIXTURES / "petstore.json",
        REPO / "examples" / "petstore.json",
    ], ids=["fixture", "example"])
    @pytest.mark.parametrize("mode", ["stub", "map", "none"])
    def test_checks_and_builds(self, tmp_path, spec, mode):
        path, _ = derive(tmp_path, spec, f"pets-{mode}", "-s", mode)
        assert_checks(path, holes_allowed=True)
        path.write_text(add_main(fill_holes(path.read_text())))
        assert build_and_run(path, tmp_path) == 0

    def test_map_mode_storage_round_trip(self, tmp_path):
        path, _ = derive(tmp_path, "petstore.json", "pets", "-s", "map")
        body = """(with-arena 4096
      (let ((s (state-new arena))
            (np (cast (Ptr NewPet) (arena-alloc arena (sizeof NewPet)))))
        (set! np name "Rex")
        (set! np species 'dog)
        (set! np weight (some 3.5))
        (let ((p (state-insert-pet arena s np)))
          (match (state-get-pet s (. p id))
            ((some got) (if (== (. got name) "Rex") 0 2))
            ((none) 1)))))"""
        path.write_text(add_main(fill_holes(path.read_text()), body))
        assert build_and_run(path, tmp_path) == 0

    def _run_example(self, path, impl):
        text = fill_holes(path.read_text(), impl, only="get-api-v1-pets-by-pet-id")
        path.write_text(fill_holes(text))
        result = slop("test", path)
        return result.stdout + result.stderr

    def test_none_mode_example_runs(self, tmp_path):
        """The derived @example is runnable by slop test once the hole is filled."""
        path, _ = derive(tmp_path, "petstore.json", "pets", "-s", "none")
        impl = ('(ok (record-new Pet (id pet-id) (name "Fluffy \\"the cat\\"") '
                "(species 'cat) (weight (some 4.5)) (tags (none)) (born-at (none))))")
        assert "1 passed, 0 failed, 0 unrunnable" in self._run_example(path, impl)

    def test_none_mode_example_asserts_the_record(self, tmp_path):
        # Without the list field and the ranged name there is no `_` in the
        # expected record, so every field is compared and a wrong species
        # fails the example. (With a `_` anywhere inside (ok ...), slop test
        # checks the tag only.)
        spec = _petstore()
        del spec["components"]["schemas"]["Pet"]["properties"]["tags"]
        del spec["components"]["schemas"]["Pet"]["properties"]["name"]["maxLength"]
        del spec["components"]["schemas"]["Pet"]["properties"]["name"]["minLength"]
        get = spec["paths"]["/api/v1/pets/{petId}"]["get"]
        del get["responses"]["200"]["content"]["application/json"]["example"]["tags"]
        source = tmp_path / "pets.json"
        source.write_text(json.dumps(spec))
        path, _ = derive(tmp_path, source, "pets", "-s", "none")
        assert "(tags _)" not in path.read_text() and "(name _)" not in path.read_text()

        impl = ('(ok (record-new Pet (id pet-id) (name "Fluffy \\"the cat\\"") '
                "(species 'cat) (weight (some 4.5)) (born-at (none))))")
        assert "1 passed, 0 failed, 0 unrunnable" in self._run_example(path, impl)
        path, _ = derive(tmp_path, source, "pets", "-s", "none")
        wrong = impl.replace("'cat", "'dog")
        assert "0 passed, 1 failed" in self._run_example(path, wrong)
